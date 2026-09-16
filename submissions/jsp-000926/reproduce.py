"""Compile and replay this exact five-module package with an existing pinned cache.

The caller coordinates any machine-wide Lean mutex. This helper acquires none.
It rebuilds every package module in a fresh output directory, including the
unchanged prerequisite, and never modifies the supplied Mathlib/runtime trees.
Imported Mathlib binaries are a disclosed trust boundary, not a fresh rebuild.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, sys, time
from bootstrap_upstream import bootstrap

MODULES = ('Upstream', 'GeometricLength', 'LengthProperties', 'CurveStatement', 'Audit')
TARGETS = ('Erdos1115.labyrinth_isGeometricLengthBarrier',
    'Erdos1115.not_erdos_1115_geometric', 'Erdos1115.not_erdos_1115_continuousOn',
    'Erdos1115.curve_escapes_of_composition_escapes',
    'Erdos1115.geometricLengthInDisc_mono',
    'Erdos1115.geometricLengthInDisc_ne_top_of_locallyBoundedVariationOn')
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB_COMMIT = 'db584cd6d46c92f209a44c0f1c829460d327499d'
MATHLIB_MANIFEST = '56f0aa1ff2fe546d0356da6f12f15c1242a3a6d6199315ec9860be9c31209453'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--mathlib-dir', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    runtime, mathlib = args.lean_bin.resolve(), args.mathlib_dir.resolve()
    pin = bootstrap()
    got = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    if got != MATHLIB_COMMIT or digest(mathlib/'lake-manifest.json') != MATHLIB_MANIFEST:
        raise SystemExit('Mathlib revision/manifest mismatch')
    extension = '.exe' if os.name == 'nt' else ''
    lean, checker = runtime/('lean'+extension), runtime/('leanchecker'+extension)
    env = os.environ.copy()
    env['LEAN_SYSROOT'] = str(runtime.parent)
    version = subprocess.check_output([str(lean), '--version'], text=True, env=env).strip()
    if 'version 4.33.0' not in version or 'd8b18978322de05a8f3dba51ef03cf5461676c17' not in version:
        raise SystemExit('Lean 4.33.0 required')
    started = datetime.now(timezone.utc)
    run = root/'.reproduction'/started.strftime('%Y%m%dT%H%M%S%fZ')
    run.mkdir(parents=True, exist_ok=False)
    build = run/'lib/lean'
    (build/'JSP000926').mkdir(parents=True)
    source_hashes = {f'JSP000926/{name}.lean': digest(root/f'JSP000926/{name}.lean') for name in MODULES}
    paths = [build, mathlib/'.lake/build/lib/lean']
    for p in sorted((mathlib/'.lake/packages').iterdir()):
        if p.is_dir():
            paths.append(p/'.lake/build/lib/lean')
    paths.append(root)
    env['PATH'] = str(runtime)+os.pathsep+env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    env['LEAN_NUM_THREADS'] = '1'
    meta = dict(started_at_utc=started.isoformat(), lean_version=version,
        mathlib_commit=MATHLIB_COMMIT, mathlib_manifest_sha256=MATHLIB_MANIFEST,
        prerequisite=pin, source_sha256=source_hashes, steps=[],
        helper_sha256=digest(root/'reproduce.py'), bootstrap_sha256=digest(root/'bootstrap_upstream.py'),
        tool_sha256={lean.name:digest(lean), checker.name:digest(checker)},
        environment={'os':sys.platform, 'network_disabled':False, 'LEAN_NUM_THREADS':'1',
            'LEAN_SYSROOT':'explicit parent of supplied lean-bin directory'},
        limitations=['Existing pinned Mathlib/dependency binaries were imported; no full source rebuild.',
            'lean and leanchecker use the same Lean kernel, not independent implementations.',
            'This is contributor-run verification, not organizer certification.'])
    def redact(text):
        for prefix, label in ((root, '.'), (mathlib, '<mathlib>'), (runtime, '<lean-bin>')):
            text = text.replace(str(prefix), label).replace(prefix.as_posix(), label)
        return text
    def save():
        (run/'verification.json').write_text(json.dumps(meta, indent=2)+'\n', encoding='utf-8')
    for mode in ('compile', 'replay'):
        for short in MODULES:
            module = 'JSP000926.'+short
            source = root/'JSP000926'/f'{short}.lean'
            artifact = build/'JSP000926'/f'{short}.olean'
            command = ([str(lean), '-o', str(artifact), str(source)] if mode == 'compile'
                       else [str(checker), '--verbose', module])
            if mode == 'replay' and (build/'JSP000926'/short).exists():
                raise SystemExit('Unexpected descendant prefix: refusing broader replay')
            before = {key:digest(root/key) for key in source_hashes}
            binaries = {p.relative_to(build).as_posix():digest(p) for p in build.rglob('*.olean*')}
            clock = time.monotonic()
            result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True,
                encoding='utf-8', errors='replace')
            output = redact(result.stdout+result.stderr)
            logfile = f'{short}-{mode}.log'
            (run/logfile).write_text(output, encoding='utf-8', newline='\n')
            step = dict(module=module, mode=mode, tool=Path(command[0]).name,
                arguments=[redact(x) for x in command[1:]],
                exit_code=result.returncode, duration_seconds=round(time.monotonic()-clock,3),
                source_sha256=digest(source), log=logfile,
                imported_project_artifacts=binaries)
            after = {key:digest(root/key) for key in source_hashes}
            step['source_identity_unchanged'] = before == after == source_hashes
            binaries_after = {p.relative_to(build).as_posix():digest(p) for p in build.rglob('*.olean*')}
            if mode == 'replay':
                step['artifact_identity_unchanged'] = binaries == binaries_after
                step['replayed_modules'] = re.findall(r'^replaying (\S+)\s*$', output, re.MULTILINE)
                step['exact_replay_match'] = step['replayed_modules'] == [module]
            else:
                step['artifact_identity_unchanged'] = all(binaries_after.get(k) == v for k,v in binaries.items())
            meta['steps'].append(step)
            save()
            print(json.dumps({key:step[key] for key in ('module','mode','exit_code','duration_seconds')}), flush=True)
            if (result.returncode or not step['source_identity_unchanged']
                    or not step['artifact_identity_unchanged'] or step.get('exact_replay_match') is False):
                print(output, flush=True)
                raise SystemExit(1)
            if mode == 'compile' and (not artifact.is_file() or artifact.stat().st_size == 0):
                raise SystemExit('Missing compilation output')
            if mode == 'compile' and short == 'Audit':
                audits = {}
                for target in TARGETS:
                    match = re.search(re.escape("'"+target+"'")+r' depends on axioms: \[([^\]]*)\]', output)
                    if not match:
                        raise SystemExit('Missing target audit: '+target)
                    axioms = {x.strip() for x in match[1].split(',') if x.strip()}
                    if not axioms <= STANDARD_AXIOMS:
                        raise SystemExit('Unexpected axioms: '+target)
                    audits[target] = sorted(axioms)
                meta['target_axioms'] = audits
                save()
    meta['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    meta['all_steps_passed'] = True
    meta['module_artifacts'] = {p.relative_to(build).as_posix():digest(p) for p in build.rglob('*.olean*')}
    save()
    print('VERIFIED '+(run/'verification.json').relative_to(root).as_posix(), flush=True)

if __name__ == '__main__':
    main()
