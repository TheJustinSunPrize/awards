#!/usr/bin/env python3
"""Metadata-only by default; --execute performs a fresh E732 contribution replay.

Adapted from the reviewed JSP-000422 portable helper. Python 3.10+.
No Lake, installation, Mathlib download or shared-cache writes. recipe.json pins
the four included contribution modules, the Audit and one downloaded dependency.
--plan runs no subprocess and performs no download or filesystem mutation.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time
import urllib.request

HERE = Path(__file__).resolve().parent
SOURCE_COMMIT = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
MATHLIB_COMMIT = 'db584cd6d46c92f209a44c0f1c829460d327499d'
LEAN_VERSION = '4.33.0'
UPSTREAM = 'ErdosProblems.Erdos732'
CONTRIBUTIONS = ['Contribution732.FinitePlane', 'Contribution732.Profiles',
                 'Contribution732.Counting', 'Contribution732.PrimePowers']
ORDER = [UPSTREAM, *CONTRIBUTIONS]
RAW_URL = ('https://raw.githubusercontent.com/plby/lean-proofs/' + SOURCE_COMMIT +
           '/src/latest/ErdosProblems/Erdos732.lean')
UPSTREAM_SHA = '752d9a781a713dd96e55b482e584ccc4227cb2b698795f6c0cd474d18945db34'
UPSTREAM_BLOB = '244874dd6a25f2659d6d00f1897bf489e930c181'
UPSTREAM_BYTES = 26189
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
HASH = re.compile(r'[0-9a-f]{64}')
REQUIRED_DECLARATIONS = {
    'Contribution732.card_PG', 'Contribution732.card_linePoints',
    'Contribution732.exists_compatible_of_profile',
    'Contribution732.determined_by_primary_profile',
    'Contribution732.completeProfile_compatible',
    'Contribution732.profileSizes_injective', 'Contribution732.card_profileCode',
    'Contribution732.complete_profile_family', 'Contribution732.card_galoisField',
    'Contribution732.exists_compatible_of_prime_power_profile',
    'Contribution732.complete_prime_power_profile_family',
    'Contribution732.order_four_profile_family', 'Contribution732.order_five_profile_family',
    'Erdos732.erdos_732',
}
REQUIRED_DEFINITIONS = {'Erdos732.PairwiseBalancedDesign', 'Erdos732.BlockCompatible',
    'Erdos732.PairwiseBalancedDesign.blockSizes', 'Contribution732.completeProfile',
    'Contribution732.ProfileCode', 'Contribution732.profileSizes'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


def under(root, relative):
    require(isinstance(relative, str) and bool(relative), 'Missing relative path')
    pure = PurePosixPath(relative)
    require(not pure.is_absolute() and str(pure) == relative and
            all(x not in ('.', '..') for x in pure.parts) and
            not any(x in relative for x in ('\\', ':', '\0')), 'Unsafe relative path')
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), 'Path escapes its root')
    return path


def parse_axioms(text, names):
    parsed, raw = {}, {}
    for match in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", text, re.S):
        if match[1] not in names:
            continue
        require(match[1] not in parsed, 'Duplicate requested axiom report')
        atoms = []
        for token in re.split(r',\s*(?![^{}]*\})', match[2] or ''):
            if not token.strip():
                continue
            atom = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)(?:\.\{[^{}]+\})?', token.strip())
            require(atom is not None, 'Malformed printed axiom')
            atoms.append(atom[1])
        require(len(set(atoms)) == len(atoms) and set(atoms) <= ALLOWED,
                'Nonstandard or repeated axiom')
        parsed[match[1]], raw[match[1]] = atoms, match[0]
    require(set(parsed) == set(names), 'Missing requested axiom report')
    return {n: parsed[n] for n in names}, {n: raw[n] for n in names}


def selection(text, expected):
    actual = re.findall(r'(?m)^replaying ([A-Za-z_0-9.]+)\s*$', text)
    require(len(actual) == len(set(actual)) and set(actual) == set(expected),
            'Actual checker selection differs')
    return actual


def printed_definitions(text, names):
    found = {}
    for match in re.finditer(r'(?m)^(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected) )?(?:def|abbrev|opaque|structure|inductive|class) ([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)[^\n]*', text):
        if match[1] not in names:
            continue
        require(match[1] not in found, 'Duplicate requested printed definition')
        found[match[1]] = match[0]
    require(set(found) == set(names), 'Missing requested printed definition')
    return {name: found[name] for name in names}


def strip_comments_strings(text):
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2; out.append('  ')
            elif text.startswith('-/', i): depth -= 1; i += 2; out.append('  ')
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\': out.append('  '); i += 2
            else: quoted = text[i] != '"'; out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1: out.append(' ' * (len(text) - i)); break
            out.append(' ' * (end - i)); i = end
        elif text.startswith('/-', i): depth = 1; i += 2; out.append('  ')
        elif text[i] == '"': quoted = True; i += 1; out.append(' ')
        else: out.append(text[i]); i += 1
    require(depth == 0 and not quoted, 'Unclosed source comment or string')
    return ''.join(out)


def inspect_source(data, row, seen):
    require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Source digest/size mismatch')
    clean = strip_comments_strings(data.decode('utf-8'))
    require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|sorryAx|ofReduceBool|ofReduceNat|extern)\b', clean), 'Untrusted proof marker')
    require(not re.search(r'\bset_option\s+debug\.skipKernelTC\s+true\b', clean), 'Disabled kernel checks')
    require(not re.search(r'(?m)^\s*(?:#eval\b|run_cmd\b|run_elab\b|initialize\b|builtin_initialize\b|elab\b|macro\b|syntax\b)', clean), 'Active metaprogramming command')
    imports = []
    for match in re.finditer(r'(?m)^\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?([^\n]+)', clean):
        imports.extend(NAME.findall(match[1]))
    require(imports == row['imports'], 'Source imports changed')
    require(all(m in seen or m == 'Mathlib' or m.startswith('Mathlib.') for m in imports),
            'Incomplete/topologically invalid custom closure')


def audit_text(audit):
    lines = ['import Contribution732.PrimePowers', '', 'set_option pp.universes true', '']
    for name in audit['definitions_printed']:
        lines += ['#print ' + name, '']
    for name in audit['declarations']:
        lines += ['#check @' + name, '#print axioms ' + name, '']
    return '\n'.join(lines)


def validate_recipe(recipe, base=HERE):
    """Read included source bytes only. No processes, download or output creation."""
    require(recipe['schema_version'] == 1 and recipe['jsp'] == 'JSP-000600' and recipe['erdos'] == 732,
            'Wrong recipe identity/schema')
    require(recipe['source_commit'] == SOURCE_COMMIT and recipe['mathlib_commit'] == MATHLIB_COMMIT,
            'Wrong source or Mathlib pin')
    require(recipe['lean_version'] == LEAN_VERSION and recipe['lean_toolchain'] == 'leanprover/lean4:v4.33.0', 'Wrong Lean version')
    sources = recipe['sources']
    require([r['module'] for r in sources] == recipe['build_order'] == ORDER, 'Wrong five-module build order')
    require(set(recipe['axiom_whitelist']) == ALLOWED, 'Changed axiom whitelist')
    seen = set()
    for row in sources:
        require(HASH.fullmatch(row['sha256']) is not None and type(row['bytes']) is int and row['bytes'] > 0,
                'Bad source digest/size')
        require(row['relative_file'] == row['module'].replace('.', '/') + '.lean', 'Module/file mismatch')
        require(isinstance(row['imports'], list) and all(isinstance(n, str) and NAME.fullmatch(n) for n in row['imports']), 'Unsafe import name')
        path = under(base, row['relative_file'])
        if row['module'] == UPSTREAM:
            require(row['kind'] == 'download' and not path.exists(), 'Upstream must be downloaded, not vendored')
            require(row['raw_url'] == RAW_URL and row['source_url'] ==
                    'https://github.com/plby/lean-proofs/blob/' + SOURCE_COMMIT + '/src/latest/ErdosProblems/Erdos732.lean', 'Unpinned upstream URL')
            require((row['sha256'], row['git_blob_sha1'], row['bytes']) ==
                    (UPSTREAM_SHA, UPSTREAM_BLOB, UPSTREAM_BYTES), 'Changed original upstream source identity')
            require(row['imports'] == ['Mathlib'], 'Wrong upstream import')
        else:
            require(row['kind'] == 'included_contribution', 'Wrong contribution source kind')
            inspect_source(path.read_bytes(), row, seen)
        seen.add(row['module'])
    audit = recipe['audit']
    require(NAME.fullmatch(audit['module']) and audit['module'] not in ORDER and
            not audit['module'].startswith('Contribution732.'), 'Audit must be outside replay prefixes')
    require(audit['module'] != 'Contribution732' and not audit['module'].startswith(UPSTREAM + '.'), 'Audit overlaps replay root')
    require(audit['file'] == audit['module'].replace('.', '/') + '.lean', 'Audit module/file mismatch')
    require(HASH.fullmatch(audit['sha256']) is not None, 'Bad Audit digest')
    for field, mandatory in [('declarations', REQUIRED_DECLARATIONS), ('definitions_printed', REQUIRED_DEFINITIONS)]:
        names = audit[field]
        require(isinstance(names, list) and len(names) == len(set(names)) and
                all(isinstance(n, str) and NAME.fullmatch(n) for n in names), 'Invalid or duplicate audit name')
        require(mandatory <= set(names), 'Missing substantive contribution audit declaration/definition')
        require(all(n.startswith('Contribution732.') or n.startswith('Erdos732.') for n in names), 'Audit name outside submission scope')
    data = under(base, audit['file']).read_bytes()
    require(sha(data) == audit['sha256'], 'Audit source hash mismatch')
    normalize = lambda text: [' '.join(line.split()) for line in strip_comments_strings(text).splitlines() if line.strip()]
    require(normalize(data.decode('utf-8')) == normalize(audit_text(audit)), 'Audit commands differ from declared audit')
    roots = recipe['checker_targets']
    require([r['module'] for r in roots] == ['Contribution732', UPSTREAM], 'Wrong checker roots')
    for target in roots:
        expected = [m for m in ORDER if m == target['module'] or m.startswith(target['module'] + '.')]
        require(target['expected_selected_modules'] == expected, 'Wrong structured Name checker selection')
    expected_local = {r['relative_file'] for r in sources if r['kind'] == 'included_contribution'} | {audit['file']}
    require({p.relative_to(base).as_posix() for p in base.rglob('*.lean')} == expected_local,
            'Unexpected or missing vendored Lean source')
    return {'status': 'metadata_only_passed_no_execution_record', 'included_contributions': 4,
            'upstream_files_downloaded_on_execute': 1, 'planned_compile_count': 5,
            'audited_declarations': len(audit['declarations']), 'printed_definitions': len(audit['definitions_printed']),
            'planned_checker_counts': [4, 1], 'lean_started': False, 'network_used': False}


def validate_evidence(recipe, evidence, recipe_sha, base=HERE):
    require(evidence['schema_version'] == 1 and evidence['jsp'] == 'JSP-000600', 'Wrong evidence identity')
    require(evidence['status'] == 'verified_fresh_custom_compilation' and
            evidence['observed_wrapper_exit_code'] == 0, 'No successful observed wrapper completion')
    require(evidence['recipe_json_sha256'] == recipe_sha, 'Evidence/recipe mismatch')
    require(evidence['fresh_custom_compilation'] is True and evidence['private_object_reuse'] is False,
            'This recipe requires all five custom sources freshly compiled')
    require(evidence['LEAN_NUM_THREADS'] == '1' and evidence['mathlib_commit'] == MATHLIB_COMMIT and
            evidence['toolchain'] == recipe['lean_toolchain'], 'Recorded environment differs')
    require(re.search(r'\bversion\s+4\.33\.0(?:[,\s]|$)', evidence['lean_version']), 'Recorded Lean version differs')
    require(evidence['final_source_hashes_match'] is True and evidence['runtime_binary_hashes_unchanged'] is True,
            'Missing final source/runtime integrity checks')
    runtime_hashes = evidence['runtime_binary_sha256']
    require(set(runtime_hashes) in ({'lean', 'leanchecker'}, {'lean.exe', 'leanchecker.exe'}) and
            all(HASH.fullmatch(digest) for digest in runtime_hashes.values()), 'Invalid runtime executable identities')
    require(evidence['source_sha256'] == {r['module']: r['sha256'] for r in recipe['sources']} and
            evidence['audit_sha256'] == recipe['audit']['sha256'], 'Evidence/source mismatch')
    for rel, row in evidence['logs'].items():
        require(rel.startswith('logs/'), 'Published log outside logs directory')
        data = under(base, rel).read_bytes()
        require(sha(data) == row['published_sha256'] and len(data) == row['published_bytes'], 'Published log changed')
        require(HASH.fullmatch(row['original_sha256']) is not None, 'Missing original log hash')
        if row['bytes_unchanged']:
            require(not row['redactions'] and row['original_sha256'] == row['published_sha256'] and
                    row['original_bytes'] == row['published_bytes'], 'False unchanged-log claim')
        else:
            require(bool(row['redactions']), 'Unexplained log redaction')
    events = evidence['events']
    require(len(events) == 8 and all(e['exit_code'] == 0 for e in events), 'Incomplete successful events')
    require(all(e['LEAN_NUM_THREADS'] == '1' for e in events), 'Recorded stage thread count differs')
    require([e['stage'] for e in events] == ['compile'] * 5 + ['audit', 'leanchecker', 'leanchecker'], 'Wrong event sequence')
    require([e['module'] for e in events[:5]] == ORDER and events[5]['module'] == recipe['audit']['module'], 'Actual compilation coverage differs')
    require(len({e['log'] for e in events}) == 8, 'Repeated successful log')
    for event in events + evidence.get('failed_attempts', []):
        require(event['log_sha256'] == evidence['logs'][event['log']]['published_sha256'], 'Event log mismatch')
    for event in events[:6]:
        require(event['recorded_command_with_paths_redacted'][1:4] == ['-j1', '-M8192', '-o'], 'Recorded compile flags differ')
    actual, raw = parse_axioms(under(base, events[5]['log']).read_text(encoding='utf-8'), recipe['audit']['declarations'])
    require(actual == evidence['actual_axioms'] and raw == evidence['actual_axiom_reports_raw'], 'Axiom summary differs from raw log')
    definitions = printed_definitions(under(base, events[5]['log']).read_text(encoding='utf-8'), recipe['audit']['definitions_printed'])
    require(definitions == evidence['actual_definition_headers_raw'], 'Definition summary differs from raw log')
    for target, event in zip(recipe['checker_targets'], events[6:], strict=True):
        root = target['module']
        require(event['module'] == root and event['recorded_command_with_paths_redacted'][1:] == ['--verbose', root], 'Wrong checker event')
        selected = selection(under(base, event['log']).read_text(encoding='utf-8'), target['expected_selected_modules'])
        require(selected == evidence['actual_checker_modules'][root], 'Checker summary differs from log')
    require(not re.search(r'(?i)(?:(?<![A-Za-z0-9_])[a-z]:[\\/]|/Users/|/home/)', json.dumps(evidence)), 'Private path in public evidence')
    return {'status': 'metadata_and_published_logs_passed', 'actual_compile_count': 5,
            'actual_checker_counts': [4, 1], 'lean_started': False, 'network_used': False}


def load(base=HERE):
    raw = (base / 'recipe.json').read_bytes()
    recipe = json.loads(raw)
    summary = validate_recipe(recipe, base)
    path = base / 'verification.json'
    if path.exists():
        summary.update(validate_evidence(recipe, json.loads(path.read_text(encoding='utf-8')), sha(raw), base))
    summary['recipe_json_sha256'] = sha(raw)
    return recipe, summary


def tool_path(directory, name):
    return directory / (name + '.exe' if (directory / (name + '.exe')).is_file() else name)


def command_plan(recipe, lean_bin, output):
    src, build = output / 'src', output / 'build'
    stages = [{'stage': 'compile', 'module': r['module'], 'command':
        [str(tool_path(lean_bin, 'lean')), '-j1', '-M8192', '-o',
         str(build / Path(r['relative_file']).with_suffix('.olean')), r['relative_file']]}
        for r in recipe['sources']]
    audit = recipe['audit']
    stages.append({'stage': 'audit', 'module': audit['module'], 'command':
        [str(tool_path(lean_bin, 'lean')), '-j1', '-M8192', '-o',
         str(build / Path(audit['file']).with_suffix('.olean')), audit['file']]})
    stages += [{'stage': 'leanchecker', 'module': t['module'], 'command':
        [str(tool_path(lean_bin, 'leanchecker')), '--verbose', t['module']],
        'expected_selected_modules': t['expected_selected_modules']} for t in recipe['checker_targets']]
    return src, build, stages


class RejectRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def download(row):
    require(row['raw_url'] == RAW_URL and row['bytes'] == UPSTREAM_BYTES, 'Download outside fixed URL/size')
    opener = urllib.request.build_opener(RejectRedirects())
    with opener.open(row['raw_url'], timeout=60) as response:
        require(response.status == 200, 'Source download did not return HTTP 200')
        require(response.geturl() == RAW_URL, 'Source response URL differs from pinned URL')
        return response.read(row['bytes'] + 1)


def materialize(recipe, source_root, package=HERE, fetch=download):
    seen = set()
    for row in recipe['sources']:
        data = fetch(row) if row['kind'] == 'download' else under(package, row['relative_file']).read_bytes()
        inspect_source(data, row, seen)
        if row['kind'] == 'download':
            require(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob_sha1'], 'Upstream Git blob mismatch')
        target = under(source_root, row['relative_file'])
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
        seen.add(row['module'])
    audit = recipe['audit']
    data = under(package, audit['file']).read_bytes()
    require(sha(data) == audit['sha256'], 'Audit changed')
    target = under(source_root, audit['file'])
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as stream:
        stream.write(data)


def check_output_location(output, mathlib, lean_bin, package):
    require(not output.exists() and not output.is_symlink(), 'Output exists; choose a fresh dedicated directory')
    require(all(not output.is_relative_to(p) for p in (mathlib, lean_bin, package)),
            'Output must be outside Mathlib, runtime and this package')


def execute(recipe, mathlib, lean_bin, output, package=HERE, fetch=download):
    mathlib, lean_bin, output, package = (p.resolve() for p in (mathlib, lean_bin, output, package))
    validate_recipe(recipe, package)
    check_output_location(output, mathlib, lean_bin, package)
    recipe_bytes = (package / 'recipe.json').read_bytes()
    require(json.loads(recipe_bytes) == recipe, 'Recipe differs from file')
    env = os.environ.copy()
    env.update(LEAN_NUM_THREADS='1', GIT_OPTIONAL_LOCKS='0')
    for name in ('LEAN_SYSROOT', 'LEAN_SRC_PATH', 'LEAN_PATH'):
        env.pop(name, None)
    env['PATH'] = str(lean_bin) + os.pathsep + env.get('PATH', '')
    head = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, env=env).strip()
    require(head == MATHLIB_COMMIT, 'Wrong Mathlib commit')
    require((mathlib / 'lean-toolchain').read_text(encoding='utf-8').strip() == recipe['lean_toolchain'], 'Wrong toolchain file')
    lean, checker = tool_path(lean_bin, 'lean'), tool_path(lean_bin, 'leanchecker')
    require(lean.is_file() and checker.is_file(), 'Missing explicit Lean/checker executable')
    version = subprocess.check_output([str(lean), '--version'], text=True, env=env).strip()
    require(re.search(r'\bversion\s+4\.33\.0(?:[,\s]|$)', version), 'Actual Lean is not 4.33.0')
    caches = [mathlib / '.lake/build/lib/lean']
    require((caches[0] / 'Mathlib.olean').is_file(), 'Mathlib cache is not installed')
    if (mathlib / '.lake/packages').is_dir():
        caches += sorted(p / '.lake/build/lib/lean' for p in (mathlib / '.lake/packages').iterdir()
                         if (p / '.lake/build/lib/lean').is_dir())
    src, build, stages = command_plan(recipe, lean_bin, output)
    output.mkdir(parents=True, exist_ok=False)
    src.mkdir(); build.mkdir(); logs = output / 'logs'; logs.mkdir()
    result = {'schema_version': 1, 'jsp': 'JSP-000600', 'status': 'running',
        'recipe_json_sha256': sha(recipe_bytes), 'fresh_custom_compilation': True, 'private_object_reuse': False,
        'lean_version': version, 'mathlib_commit': head, 'toolchain': recipe['lean_toolchain'],
        'LEAN_NUM_THREADS': '1', 'runtime_binary_sha256': {p.name: sha(p.read_bytes()) for p in (lean, checker)},
        'source_sha256': {r['module']: r['sha256'] for r in recipe['sources']},
        'audit_sha256': recipe['audit']['sha256'], 'events': [], 'actual_axioms': None, 'actual_checker_modules': {}}
    save(output / 'result.json', result)
    try:
        materialize(recipe, src, package, fetch)
        env['LEAN_PATH'] = os.pathsep.join(map(str, [build, src, *caches]))
        compiled = set()
        for i, stage in enumerate(stages):
            command = stage['command']
            if stage['stage'] != 'leanchecker':
                Path(command[4]).parent.mkdir(parents=True, exist_ok=True)
            if stage['stage'] == 'compile':
                require(all(m in compiled or m == 'Mathlib' or m.startswith('Mathlib.') for m in recipe['sources'][i]['imports']), 'Refuse cached custom-import fallback')
            log = logs / f'{i:02d}-{stage["stage"]}-{stage["module"]}.log'
            event = {**stage, 'start_utc': datetime.now(timezone.utc).isoformat(), 'exit_code': None,
                     'log': log.relative_to(output).as_posix(), 'LEAN_NUM_THREADS': '1'}
            result['events'].append(event); save(output / 'result.json', result)
            print(f'START {i + 1}/{len(stages)} {stage["stage"]} {stage["module"]}', flush=True)
            start = time.monotonic()
            with log.open('xb') as stream:
                child = subprocess.run(command, cwd=src, env=env, stdout=stream, stderr=subprocess.STDOUT)
            event.update(exit_code=child.returncode, seconds=round(time.monotonic() - start, 3),
                end_utc=datetime.now(timezone.utc).isoformat(), log_sha256=sha(log.read_bytes()), log_bytes=log.stat().st_size)
            save(output / 'result.json', result)
            require(child.returncode == 0, f'{stage["stage"]} failed: {stage["module"]}; see {log}')
            text = log.read_text(encoding='utf-8')
            if stage['stage'] in ('compile', 'audit'):
                require(Path(command[4]).is_file(), 'Missing expected fresh output object')
            if stage['stage'] == 'compile':
                compiled.add(stage['module'])
            elif stage['stage'] == 'audit':
                result['actual_axioms'], result['actual_axiom_reports_raw'] = parse_axioms(text, recipe['audit']['declarations'])
                result['actual_definition_headers_raw'] = printed_definitions(text, recipe['audit']['definitions_printed'])
            else:
                result['actual_checker_modules'][stage['module']] = selection(text, stage['expected_selected_modules'])
            print(f'END {i + 1}/{len(stages)} exit={child.returncode}', flush=True)
            save(output / 'result.json', result)
        validate_recipe(recipe, package)
        require(sha((package / 'recipe.json').read_bytes()) == result['recipe_json_sha256'], 'Recipe changed during execution')
        for row in recipe['sources']:
            require(sha(under(src, row['relative_file']).read_bytes()) == row['sha256'], 'Materialized source changed')
        require(sha(under(src, recipe['audit']['file']).read_bytes()) == recipe['audit']['sha256'], 'Materialized Audit changed')
        for event in result['events']:
            require(sha(under(output, event['log']).read_bytes()) == event['log_sha256'], 'Recorded log changed')
        require(subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, env=env).strip() == head, 'Mathlib changed during execution')
        require((mathlib / 'lean-toolchain').read_text(encoding='utf-8').strip() == recipe['lean_toolchain'], 'Toolchain file changed')
        for tool in (lean, checker):
            require(sha(tool.read_bytes()) == result['runtime_binary_sha256'][tool.name], 'Runtime executable changed')
        result['build_artifacts'] = [{'file': p.relative_to(output).as_posix(), 'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
                                     for p in sorted(build.rglob('*')) if p.is_file()]
        result.update(status='verified_fresh_custom_compilation', final_source_hashes_match=True,
                      runtime_binary_hashes_unchanged=True, ended_utc=datetime.now(timezone.utc).isoformat())
        save(output / 'result.json', result)
        return result
    except Exception as error:
        result.update(status='failed', error=f'{type(error).__name__}: {error}', ended_utc=datetime.now(timezone.utc).isoformat())
        save(output / 'result.json', result)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--execute', action='store_true')
    mode.add_argument('--plan', action='store_true')
    parser.add_argument('--mathlib', type=Path, help='Already cached pinned Mathlib checkout; read-only')
    parser.add_argument('--lean-bin', type=Path, help='Explicit Lean 4.33.0 and leanchecker directory')
    parser.add_argument('--output', type=Path, help='Fresh directory outside Mathlib, runtime and this package')
    args = parser.parse_args()
    recipe, summary = load()
    if not args.execute and not args.plan:
        print(json.dumps(summary, indent=2)); return
    require(all(p is not None for p in (args.mathlib, args.lean_bin, args.output)),
            '--plan/--execute requires --mathlib, --lean-bin and --output')
    mathlib, lean_bin, output = (p.resolve() for p in (args.mathlib, args.lean_bin, args.output))
    check_output_location(output, mathlib, lean_bin, HERE.resolve())
    if args.plan:
        src, build, stages = command_plan(recipe, lean_bin, output)
        print(json.dumps({'status': 'plan_only_not_executed', 'cwd': str(src), 'build': str(build),
            'LEAN_NUM_THREADS': '1', 'fresh_custom_compile_count': 5, 'stage_count': 8,
            'stages': stages, 'network_used': False, 'lean_started': False}, indent=2)); return
    result = execute(recipe, mathlib, lean_bin, output)
    print(json.dumps({'status': result['status'], 'event_count': len(result['events']),
                     'result_file': str(output / 'result.json')}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
