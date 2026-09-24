#!/usr/bin/env python3
"""Fetch locked public sources; compile and replay a complete attributed proof.

Needs Python 3, gh (for GitHub API reads), a pinned Mathlib checkout with built
imports, and the specified Lean toolchain. Never modifies catalog/award records.
"""
import argparse
import base64
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(text):
    # Lean block comments nest. Strings are retained; none of these sources uses
    # forbidden-keyword string literals. A false positive stops verification.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth:
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError('unterminated block comment')
    return ''.join(out)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mathlib', type=Path, required=True)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--work', type=Path, required=True,
                   help='dedicated writable source/build directory')
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--timeout', type=int, default=600)
    p.add_argument('--fetch-only', action='store_true')
    p.add_argument('--resume-receipt', type=Path,
                   help='optional receipt from this session; default rebuilds every module')
    args = p.parse_args()
    work, evidence = args.work.resolve(), args.evidence.resolve()
    mathlib, lean = args.mathlib.resolve(), args.lean.resolve()
    lock = json.loads((HERE / 'source-lock.json').read_text())
    if not lock['complete_source_closure'] or lock['pending'] or lock['errors']:
        raise SystemExit('Source lock is not a complete closure')
    env = dict(os.environ)
    env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '2'
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if not re.search(r'version 4\.34\.0,', version):
        raise SystemExit('Unexpected Lean version: ' + version)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib,
                                     text=True).strip()
    if commit != lock['mathlib_commit']:
        raise SystemExit('Unexpected Mathlib commit')
    subprocess.run(['git', 'diff', '--exit-code', '--quiet'], cwd=mathlib, check=True)
    work.mkdir(parents=True, exist_ok=True)
    evidence.mkdir(parents=True, exist_ok=True)
    patches = json.loads((HERE / 'compatibility.json').read_text())
    for module, item in lock['modules'].items():
        if not re.fullmatch(r'[A-Za-z0-9_.]+', module) or '..' in module:
            raise SystemExit('Unsafe module path')
        target = work / (module.replace('.', '/') + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            response = subprocess.check_output([
                'gh', 'api', 'repos/plby/lean-proofs/git/blobs/' + item['git_blob']],
                text=True, timeout=60)
            data = base64.b64decode(json.loads(response)['content'])
            git_hash = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if git_hash != item['git_blob']:
                raise SystemExit('Git blob mismatch: ' + module)
            target.write_bytes(data)
        if digest(target) == item['sha256'] and module in patches:
            text = target.read_text()
            for edit in patches[module]:
                if text.count(edit['old']) != edit['count']:
                    raise SystemExit('Patch context mismatch: ' + module)
                text = text.replace(edit['old'], edit['new'])
            target.write_text(text)
        if digest(target) != item.get('patched_sha256', item['sha256']):
            raise SystemExit('Source mismatch: ' + module)
        code = without_comments(target.read_text())
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|skipKernelTC', code):
            raise SystemExit('Forbidden source construct: ' + module)
    print('All locked source hashes match.', flush=True)
    if args.fetch_only:
        return
    target = work / 'JSP000878/Main.lean'
    target.parent.mkdir(exist_ok=True)
    shutil.copyfile(HERE / 'Main.lean', target)
    shutil.copyfile(HERE / 'Statement.lean', target.with_name('Statement.lean'))
    for own in [target, target.with_name('Statement.lean')]:
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|skipKernelTC',
                     without_comments(own.read_text())):
            raise SystemExit('Forbidden construct in statement or bridge')
    env_path = subprocess.check_output([str(lean.parent / 'lake'), 'env', 'printenv',
                                       'LEAN_PATH'], cwd=mathlib, env=env, text=True).strip()
    env['LEAN_PATH'] = os.pathsep.join([str(work)] + [
        str((mathlib / entry).resolve()) for entry in env_path.split(os.pathsep)])
    receipt = {
        'started_at_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': version, 'lean_sha256': digest(lean),
        'mathlib_commit': commit, 'source_pin': lock['pin'],
        'leanchecker_sha256': digest(lean.with_name('leanchecker')),
        'bridge_sha256': digest(target), 'statement_sha256': digest(target.with_name('Statement.lean')), 'stages': [], 'verified': False,
        'independent_review': None, 'network_disabled': False,
        'mathlib_imports': 'prebuilt; problem modules freshly compiled',
        'replay_scope': 'all 29 problem modules plus independent statement and bridge; imported Mathlib reused',
        'checker': 'same-toolchain leanchecker, not an independent verifier',
        'meaning_of_verified': 'local technical checks passed, not designated review or prize eligibility',
    }
    def save():
        (evidence / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    def run(name, command, timeout):
        start = time.monotonic()
        try:
            proc = subprocess.run(command, cwd=work, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=timeout)
            code, output = proc.returncode, proc.stdout
        except subprocess.TimeoutExpired as exc:
            code, output = 'TIMEOUT', exc.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
        for private, label in [(str(work), '<proof>'), (str(mathlib), '<mathlib>'),
                               (str(lean.parent.parent), '<toolchain>')]:
            output = output.replace(private, label)
        log = evidence / (name + '.log')
        log.write_text(output + '\nexit_code=' + str(code) + '\n')
        receipt['stages'].append({'name': name, 'exit_code': code,
                                  'seconds': round(time.monotonic() - start, 3),
                                  'log_sha256': digest(log)})
        save()
        print(name, code, flush=True)
        return code, output
    previous = {}
    if args.resume_receipt:
        old = json.loads(args.resume_receipt.read_text())
        if old['lean_sha256'] != digest(lean) or old['mathlib_commit'] != commit:
            raise SystemExit('Resume receipt toolchain mismatch')
        if old['source_lock_sha256'] != digest(HERE / 'source-lock.json'):
            raise SystemExit('Resume receipt source lock mismatch')
        previous = old['modules']
        receipt['resume_receipt_sha256'] = digest(args.resume_receipt)
        receipt['mathlib_imports'] = 'prebuilt; problem modules reused only with matched local compile receipts'
    seen, order = set(), []
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for dep in lock['modules'][module]['imports']:
            visit(dep)
        order.append(module)
    for module in lock['roots']:
        visit(module)
    order.extend(['JSP000878.Statement', 'JSP000878.Main'])
    for module in order:
        relative = Path(module.replace('.', '/'))
        if module in previous and module != 'JSP000878.Main':
            prior = previous[module]
            if (prior['exit_code'] != 0 or
                    prior['source_sha256'] != digest(work / relative.with_suffix('.lean')) or
                    prior['olean_sha256'] != digest(work / relative.with_suffix('.olean'))):
                raise SystemExit('Resume receipt mismatch: ' + module)
            receipt['stages'].append(dict(prior, name='compile-' + module, reused=True))
            save()
            print('Verified prior compile receipt:', module, flush=True)
            continue
        code, output = run('compile-' + module,
                           [str(lean), '-o', str(relative.with_suffix('.olean')),
                            str(relative.with_suffix('.lean'))], args.timeout)
        if code != 0:
            raise SystemExit('Compilation failed: ' + module)
        receipt['stages'][-1]['source_sha256'] = digest(work / relative.with_suffix('.lean'))
        receipt['stages'][-1]['olean_sha256'] = digest(work / relative.with_suffix('.olean'))
        save()
        if module == 'JSP000878.Main':
            audits = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
            if len(audits) != 3:
                raise SystemExit('Missing axiom output')
            for audit in audits:
                names = {re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in audit.split(',') if x.strip()}
                if not names <= {'propext', 'Classical.choice', 'Quot.sound'}:
                    raise SystemExit('Unapproved axiom: ' + str(names))
            receipt['axiom_audits'] = audits
    code, replay_output = run('leanchecker', [str(lean.with_name('leanchecker')), '--verbose',
                                 'ErdosProblems.Erdos1058', 'JSP000878'],
                  max(args.timeout, 1800))
    if code != 0:
        raise SystemExit('Kernel replay failed')
    replayed = set(re.findall(r'^replaying (\S+)$', replay_output, re.MULTILINE))
    if replayed != set(order):
        raise SystemExit('Unexpected replay scope: ' + str(sorted(replayed)))
    receipt['replayed_modules'] = sorted(replayed)
    false = work / 'NegativeControl.lean'
    false.write_text('example : (0 : Nat) = 1 := by decide\n')
    code, _ = run('negative-control', [str(lean), 'NegativeControl.lean'], 60)
    if code == 0 or code == 'TIMEOUT':
        raise SystemExit('Negative control did not reject false arithmetic')
    receipt['negative_control_rejected'] = True
    receipt['stages'][-1]['expected_result'] = 'nonzero rejection of false arithmetic'
    receipt['verified'] = True
    receipt['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    save()


if __name__ == '__main__':
    main()
