"""Recompile and explicitly replay the three JSP248 contribution modules.

After `lake exe cache get`, run `python verify.py`. To use an already pinned
read-only dependency checkout, supply --mathlib and --lean-root. On a machine
sharing the Lean compiler with other tasks, run this script under that machine's
compiler coordinator. No network commands or shared dependency writes occur.
Each invocation keeps its own build and logs; verification/summary.json is the
latest run's state, including failures, while earlier run directories remain.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parent
MODULES = ['PrimePowerObstruction', 'SmallMultipleObstruction', 'Audit']
MATHLIB_REV = 'db584cd6d46c92f209a44c0f1c829460d327499d'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_AXIOMS = {
    'PrimePowerObstruction': {
        'JSP248.reciprocalSum_norm_of_unique_max_valuation',
        'JSP248.reciprocalSum_not_integer_of_unique_max_valuation',
        'JSP248.exists_other_large_valuation_of_reciprocalSum_eq_one',
        'JSP248.prime_power_not_largestDenominator',
        'JSP248.exceptional_infinite',
        'JSP248.one_isLargestDenominator',
    },
    'SmallMultipleObstruction': {
        'JSP248.norm_scaled_reciprocal_lt_one',
        'JSP248.small_multiple_prime_power_not_largestDenominator',
    },
    'Audit': {
        'JSP248.small_multiple_expanded',
        'JSP248.two_mul_five_pow_succ_not_largest',
        'JSP248.two_mul_five_pow_succ_injective',
    },
}
OBJECT_SUFFIXES = ('.olean', '.olean.private', '.olean.server')


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bundles(build):
    return {p.name: {'sha256': sha(p), 'bytes': p.stat().st_size}
            for module in MODULES
            for suffix in OBJECT_SUFFIXES
            if (p := build / (module+suffix)).is_file()}


def axiom_reports(text, expected):
    reports = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, text):
        fqn, listed = match.groups()
        require(fqn not in reports, 'Duplicate axiom report for '+fqn)
        observed = [x.strip() for x in (listed or '').split(',') if x.strip()]
        require(set(observed) <= STANDARD, 'Unexpected axioms for '+fqn)
        reports[fqn] = observed
    require(set(reports) == set(expected),
            'Axiom report coverage mismatch; missing='+str(sorted(set(expected)-set(reports)))+
            '; extra='+str(sorted(set(reports)-set(expected))))
    return reports


def as_bytes(value):
    return value if isinstance(value, bytes) else (value or '').encode('utf8')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mathlib', type=Path, default=ROOT/'.lake/packages/mathlib')
    ap.add_argument('--lean-root', type=Path)
    args = ap.parse_args()
    run_id = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ-')+uuid.uuid4().hex
    verification = ROOT/'verification'
    logs, build = verification/'runs'/run_id, ROOT/'build'/run_id
    logs.mkdir(parents=True)
    # A fresh build directory prevents a zero-exit compiler from being credited
    # with an old object and keeps every previous run's evidence intact.
    mathlib = args.mathlib.resolve()
    replacements = [(str(ROOT), '<package>'), (str(mathlib), '<mathlib>'),
                    (str(Path.home()), '<home>')]
    if args.lean_root is not None:
        replacements.append((str(args.lean_root.resolve()), '<toolchain>'))

    def public(value):
        for old, new in sorted(replacements, key=lambda pair: len(pair[0]), reverse=True):
            value = value.replace(old, new).replace(old.replace('\\', '/'), new)
        return value

    summary = dict(status='running', run_id=run_id,
                   run_directory=logs.relative_to(ROOT).as_posix(),
                   build_directory=build.relative_to(ROOT).as_posix(),
                   started_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   operations=[], axiom_reports={}, compiled_objects={},
                   expected_axiom_declarations=sorted(set().union(*EXPECTED_AXIOMS.values())),
                   log_policy='Complete merged output, UTF-8 decoded with replacement and known paths redacted. Hash and byte count of captured original bytes are also recorded; unredacted output is not published.',
                   trust_boundary='Imported Mathlib and standard library artifacts trusted. leanchecker uses the same Lean kernel implementation; no independent checker or complete dependency rebuild is claimed.')

    def save():
        summary['updated_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        data = json.dumps(summary, indent=2)+'\n'
        for path in (logs/'summary.json', verification/'summary.json'):
            temporary = path.with_name(path.name+'.tmp-'+run_id)
            temporary.write_text(data, encoding='utf8')
            os.replace(temporary, path)

    # Invalidate the previous latest-success view before any tool preflight.
    save()
    stage = 'preflight'
    try:
        build.mkdir(parents=True)
        require(mathlib.is_dir(), 'Obtain the pinned Mathlib checkout and caches first')
        rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib,
                                      text=True, stderr=subprocess.STDOUT, timeout=60).strip()
        summary['mathlib_revision'] = rev
        require(rev == MATHLIB_REV, 'Mathlib revision mismatch')
        root = args.lean_root
        if root is None:
            selected = shutil.which('lean')
            require(selected is not None, 'Lean is not available on PATH')
            replacements.append((selected, '<selected-lean>'))
            root = Path(subprocess.check_output([selected, '--print-prefix'], cwd=ROOT,
                                                text=True, stderr=subprocess.STDOUT, timeout=60).strip())
        root = root.resolve()
        replacements.append((str(root), '<toolchain>'))
        suffix = '.exe' if os.name == 'nt' else ''
        lean, checker = root/'bin'/('lean'+suffix), root/'bin'/('leanchecker'+suffix)
        require(lean.is_file() and checker.is_file(), 'The Lean toolchain must include leanchecker')
        source = {name+'.lean': sha(ROOT/(name+'.lean')) for name in MODULES}
        tool_hashes = {'lean': sha(lean), 'leanchecker': sha(checker)}
        summary.update(source_sha256=source, tool_sha256=tool_hashes)
        env = os.environ.copy()
        paths = [build, mathlib/'.lake/build/lib/lean']
        # Inherited packages are siblings of Mathlib in a normal Lake project;
        # a standalone Mathlib checkout has its own nested package directory.
        paths += [p/'.lake/build/lib/lean' for p in (mathlib/'.lake/packages').glob('*') if p.is_dir()]
        paths += [p/'.lake/build/lib/lean' for p in (ROOT/'.lake/packages').glob('*') if p.is_dir()]
        env.update(LEAN_PATH=os.pathsep.join(map(str, dict.fromkeys(paths))),
                   LEAN_SYSROOT=str(root), LEAN_NUM_THREADS='1')
        env['PATH'] = str(root/'bin')+os.pathsep+env.get('PATH', '')
        version = subprocess.check_output([str(lean), '--version'], cwd=ROOT,
                                          env=env, text=True, stderr=subprocess.STDOUT, timeout=60).strip()
        summary['lean_version'] = public(version)
        require(re.search(r'\bversion 4\.33\.0(?:\s|,|$)', version) and
                'd8b18978322de05a8f3dba51ef03cf5461676c17'[:7] in version,
                'Unexpected Lean version: '+version)

        def source_unchanged():
            return all((ROOT/name).is_file() and sha(ROOT/name) == digest
                       for name, digest in source.items())

        def tools_unchanged():
            return all(path.is_file() and sha(path) == tool_hashes[name]
                       for name, path in [('lean', lean), ('leanchecker', checker)])

        compiled = {}
        for mode in ['compile', 'checker']:
            for module in MODULES:
                stage = mode+'-'+module
                command = ([str(lean), '-j', '1', '-o', str(build/(module+'.olean')), str(ROOT/(module+'.lean'))]
                           if mode == 'compile' else [str(checker), module, '--verbose'])
                item = dict(mode=mode, module=module, status='running', launched=False,
                            exit_code=None, timed_out=False, timeout_seconds=600,
                            command=[public(x) for x in command],
                            objects_before=bundles(build), compiled_baseline=compiled)
                summary['operations'].append(item)
                save()
                started = time.monotonic()
                captured = b''
                try:
                    require(source_unchanged(), 'Source changed before '+stage)
                    require(tools_unchanged(), 'Toolchain changed before '+stage)
                    require(item['objects_before'] == compiled,
                            'Object bundle does not match this run\'s compilation before '+stage)
                    item['launched'] = True
                    try:
                        result = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                                stderr=subprocess.STDOUT, timeout=600)
                        captured = as_bytes(result.stdout)
                        item['exit_code'] = result.returncode
                    except subprocess.TimeoutExpired as exc:
                        captured = as_bytes(exc.output)+as_bytes(exc.stderr)
                        item['timed_out'] = True
                        raise RuntimeError('Operation timed out after 600 seconds') from exc
                    finally:
                        redacted = public(captured.decode('utf8', errors='replace')).encode('utf8')
                        log = logs/(stage+'.log')
                        log.write_bytes(redacted)
                        item.update(log=log.relative_to(ROOT).as_posix(), log_sha256=sha(log),
                                    log_bytes=len(redacted), captured_output_bytes=len(captured),
                                    captured_output_sha256=hashlib.sha256(captured).hexdigest())
                    item['objects_after'] = bundles(build)
                    item['source_unchanged'] = source_unchanged()
                    item['toolchain_unchanged'] = tools_unchanged()
                    require(item['source_unchanged'], 'Source changed during '+stage)
                    require(item['toolchain_unchanged'], 'Toolchain changed during '+stage)
                    require(item['exit_code'] == 0, stage+' returned a nonzero exit status; see its log')
                    if mode == 'compile':
                        own_names = {module+suffix for suffix in OBJECT_SUFFIXES}
                        require(module+'.olean' in item['objects_after'], 'Compilation produced no .olean')
                        require({k: v for k, v in item['objects_after'].items() if k not in own_names} == compiled,
                                'Compilation changed a previously compiled object')
                        observed = axiom_reports(captured.decode('utf8', errors='replace'), EXPECTED_AXIOMS[module])
                        require(not set(observed) & set(summary['axiom_reports']), 'Repeated declaration across modules')
                        summary['axiom_reports'].update(observed)
                        compiled = item['objects_after']
                        summary['compiled_objects'] = compiled
                    else:
                        require(item['objects_after'] == compiled, 'Replay changed the compiled object bundle')
                    item['status'] = 'passed'
                    print(f'{mode} {module}: exit 0', flush=True)
                except (Exception, KeyboardInterrupt) as exc:
                    item['status'] = 'timeout' if item['timed_out'] else 'failed'
                    item['error'] = public(str(exc))
                    raise
                finally:
                    item['elapsed_seconds'] = round(time.monotonic()-started, 3)
                    item['objects_after'] = bundles(build)
                    item['source_unchanged'] = source_unchanged()
                    item['toolchain_unchanged'] = tools_unchanged()
                    save()
        stage = 'final-binding'
        require(source_unchanged() and tools_unchanged(), 'Source or toolchain changed after operations')
        require(bundles(build) == compiled, 'Final objects differ from the compiled bundle')
        require(len(summary['operations']) == 6 and all(x['status'] == 'passed' for x in summary['operations']),
                'Incomplete compile/replay operations')
        require(set(summary['axiom_reports']) == set(summary['expected_axiom_declarations']),
                'Incomplete final axiom coverage')
        summary.update(status='passed', checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save()
        print('All three modules compiled and explicitly replayed; all 11 audited declarations use only standard axioms.')
        return 0
    except (Exception, KeyboardInterrupt) as exc:
        summary.update(status='interrupted' if isinstance(exc, KeyboardInterrupt) else 'failed',
                       failed_stage=stage, error=public(str(exc)),
                       checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        if isinstance(exc, (subprocess.CalledProcessError, subprocess.TimeoutExpired)):
            output = as_bytes(exc.output)+as_bytes(getattr(exc, 'stderr', None))
            log = logs/'preflight-failure.log'
            redacted = public(output.decode('utf8', errors='replace')).encode('utf8')
            log.write_bytes(redacted)
            command = exc.cmd if isinstance(exc.cmd, (list, tuple)) else [str(exc.cmd)]
            summary.update(preflight_log=log.relative_to(ROOT).as_posix(), preflight_log_sha256=sha(log),
                           preflight_log_bytes=len(redacted),
                           preflight_command=[public(str(part)) for part in command],
                           preflight_exit_code=getattr(exc, 'returncode', None),
                           preflight_timed_out=isinstance(exc, subprocess.TimeoutExpired),
                           preflight_timeout_seconds=getattr(exc, 'timeout', None),
                           preflight_captured_output_bytes=len(output),
                           preflight_captured_output_sha256=hashlib.sha256(output).hexdigest())
        save()
        print('Verification '+summary['status']+' at '+stage+': '+summary['error'], flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
