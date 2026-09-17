#!/usr/bin/env python3
"""Fail-closed LOCAL Lean build/type/axiom gate. No prize certification is implied.

--finite checks the complete universal finite construction without PNT downloads.
--prepare fetches dependencies and their official Mathlib cache before checking.
A definition-only package, missing audit output, or failed command cannot pass.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from lean_source import strip_comments
from preflight import config_gate, arithmetic_regression_gate

ROOT = Path(__file__).resolve().parents[1]
ALLOWLIST = {'propext', 'Classical.choice', 'Quot.sound'}
FINITE_TARGETS = ['JSP000883.finiteConstruction', 'JSP000883.admissible_candidate',
                  'JSP000883.leastN_le_of_prime']
ALL_TARGETS = FINITE_TARGETS + ['JSP000883.eventualPrimeInterval', 'JSP000883.eventualUpper',
 'JSP000883.eventually_leastN_admissible', 'JSP000883.leastN_isBigO_lcm',
 'JSP000883.lcm_isLittleO_k_mul_lcm', 'JSP000883.betterUpper',
 'JSP000883.erdos_1063_better_upper', 'chebyshev_asymptotic']
REQUIRED = {'FiniteConstruction.lean': {'finiteConstruction'},
            'PrimeInterval.lean': {'eventualPrimeInterval'},
            'Asymptotics.lean': {'eventualUpper', 'betterUpper', 'erdos_1063_better_upper'}}
FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial)\b')


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_gate(root: Path = ROOT) -> dict:
    records = []
    for path in sorted((root / 'JSP000883').glob('*.lean')):
        clean = strip_comments(path.read_text())
        bad = FORBIDDEN.search(clean)
        if bad:
            raise ValueError(f'Forbidden source token {bad.group()} in {path.name}')
        names = set(re.findall(r'^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([\w.]+)',
                               clean, re.MULTILINE))
        missing = REQUIRED.get(path.name, set()) - names
        if missing:
            raise ValueError(f'Proof declarations missing in {path.name}: {sorted(missing)}')
        records.append({'file': str(path.relative_to(root)), 'sha256': sha256(path),
                        'theorem_or_lemma_declarations': len(names)})
    for name in REQUIRED:
        if not (root / 'JSP000883' / name).is_file():
            raise ValueError(f'Missing proof module: {name}')
    return {'status': 'source_screen_only_not_kernel_verification', 'files': records}


def parse_axioms(text: str, targets: list[str]) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for name, items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text,
                                   re.MULTILINE):
        values = [part.strip() for part in items.split(',') if part.strip()]
        if name in found:
            raise ValueError(f'Duplicate audit report: {name}')
        unexpected = set(values) - ALLOWLIST
        if unexpected:
            raise ValueError(f'Unapproved axioms for {name}: {sorted(unexpected)}')
        found[name] = values
    missing = set(targets) - found.keys()
    if missing:
        raise ValueError(f'Missing axiom reports: {sorted(missing)}')
    return {name: found[name] for name in targets}


def run_command(cmd: list[str], logfile: Path, records: list[dict], *, cwd: Path = ROOT) -> str:
    record: dict = {'command': cmd, 'started_at': utc_now(), 'executed': False}
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              text=True, encoding='utf-8', errors='replace', check=False)
    except OSError as exc:
        record.update(status='blocked_could_not_start', error=str(exc), exit_code=None,
                      elapsed_seconds=time.monotonic() - start)
        records.append(record)
        logfile.write_text(f'COMMAND DID NOT START: {cmd!r}\n{exc}\n')
        raise RuntimeError(f'Could not start {cmd[0]}; no Lean result exists') from exc
    logfile.write_text(proc.stdout)
    record.update(executed=True, exit_code=proc.returncode,
                  status='process_exited', elapsed_seconds=time.monotonic() - start,
                  logfile=str(logfile.relative_to(cwd)) if logfile.is_relative_to(cwd) else logfile.name,
                  log_sha256=sha256(logfile))
    records.append(record)
    if proc.returncode != 0:
        raise RuntimeError(f'Command failed (exit {proc.returncode}): {cmd!r}; see {logfile}')
    return proc.stdout


def check_pnt_sources() -> None:
    path = ROOT / 'evidence' / 'pnt-source-manifest.json'
    if not path.exists():
        raise ValueError('PNT closure not fetched: run scripts/fetch_pnt.py, or use --prepare')
    data = json.loads(path.read_text())
    if data.get('commit') != '8822f7ddef30fadbd92e1c6ab4ed897af356af5e' or not data.get('files'):
        raise ValueError('Unpinned or empty PNT dependency closure')
    names = {r['module'] for r in data['files']}
    if 'PrimeNumberTheoremAnd.Consequences' not in names:
        raise ValueError('PNT entry module absent')
    for r in data['files']:
        p = (ROOT / r['path']).resolve()
        if not p.is_relative_to(ROOT) or not p.is_file() or sha256(p) != r['sha256']:
            raise ValueError(f'PNT source mismatch: {r["module"]}')
        for dep in r['imports']:
            if dep.startswith('PrimeNumberTheoremAnd.') and dep not in names:
                raise ValueError(f'PNT closure incomplete at {dep}')


ARITHMETIC_TARGETS = [
    'JSP000883.ProductConstruction.' + name for name in (
        'descending_product', 'ascFactorial_product', 'ascending_product',
        'auxiliary_product', 'coefficient_factor', 'split_prod',
        'Parameters.cross_identity', 'cancel_cross_product')]
GROWTH_TARGETS = ['JSP000883.lcm_isLittleO_k_mul_lcm']


def verification_stages(mode: str) -> list[dict]:
    arithmetic = {'name': 'arithmetic', 'modules': ['JSP000883.Arithmetic'],
                  'audit': 'AuditArithmetic.lean', 'targets': ARITHMETIC_TARGETS}
    finite = {'name': 'finite', 'modules': ['JSP000883.FiniteConstruction'],
              'audit': 'AuditFinite.lean', 'targets': FINITE_TARGETS}
    growth = {'name': 'growth', 'modules': ['JSP000883.Growth'],
              'audit': 'AuditGrowth.lean', 'targets': GROWTH_TARGETS}
    full = {'name': 'full', 'modules': ['JSP000883.PrimeInterval',
             'JSP000883.Asymptotics', 'JSP000883'], 'audit': 'Audit.lean',
             'targets': ALL_TARGETS, 'needs_pnt': True}
    plans = {'arithmetic': [arithmetic], 'finite': [arithmetic, finite],
             'growth': [growth], 'full': [arithmetic, finite, growth, full]}
    if mode not in plans:
        raise ValueError(f'Unknown verification mode: {mode}')
    return plans[mode]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--finite', action='store_true')
    group.add_argument('--arithmetic', action='store_true')
    group.add_argument('--growth', action='store_true')
    parser.add_argument('--prepare', action='store_true')
    args = parser.parse_args()
    mode = ('arithmetic' if args.arithmetic else 'finite' if args.finite
            else 'growth' if args.growth else 'full')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out = ROOT / 'evidence' / ('local-' + mode) / stamp
    out.mkdir(parents=True)
    records: list[dict] = []
    report: dict = {'started_at': utc_now(), 'mode': mode,
                    'status': 'not_completed', 'commands': records,
                    'completed_stages': [], 'stage_results': [],
                    'kernel_replay': 'not_run', 'independent_checker': 'not_run',
                    'official_prize_verification': False}
    code = 1
    try:
        report['configuration'] = config_gate(ROOT)
        report['arithmetic_regression_screen'] = arithmetic_regression_gate(ROOT)
        report['source_screen'] = source_gate()
        lake = shutil.which('lake') or 'lake'
        version = run_command([lake, 'env', 'lean', '--version'], out / 'version.log', records)
        if not re.search(r'\b4\.33\.0\b', version):
            raise ValueError(f'Wrong Lean version: {version.strip()}')
        if args.prepare:
            # No PNT download yet. First validate all independent finite stages.
            run_command([lake, 'exe', 'cache', 'get', 'Mathlib'], out / 'cache.log', records)
        lock = json.loads((ROOT / 'lake-manifest.json').read_text())
        report['manifest_sha256'] = sha256(ROOT / 'lake-manifest.json')
        for package in lock['packages']:
            path = ROOT / '.lake' / 'packages' / package['name']
            head = run_command(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                               out / f'dependency-{package["name"]}.log', records).strip()
            if head != package['rev']:
                raise ValueError(f'Wrong dependency revision: {package["name"]}')
        for stage in verification_stages(mode):
            report['active_stage'] = stage['name']
            if stage.get('needs_pnt'):
                if args.prepare:
                    run_command([sys.executable, 'scripts/fetch_pnt.py'],
                                out / 'fetch-pnt.log', records)
                check_pnt_sources()
            for module in stage['modules']:
                run_command([lake, 'build', module], out / f'build-{module}.log', records)
            text = run_command([lake, 'env', 'lean', '-DwarningAsError=true', stage['audit']],
                               out / f'audit-{stage["name"]}.log', records)
            axioms = parse_axioms(text, stage['targets'])
            report['stage_results'].append({'name': stage['name'],
                'status': 'local_build_exact_types_and_axiom_gate_passed', 'axioms': axioms})
            report['completed_stages'].append(stage['name'])
            report['axioms'] = axioms
        report['status'] = 'local_build_exact_types_and_axiom_gate_passed'
        code = 0
    except Exception as exc:
        blocked = bool(records and records[-1].get('status') == 'blocked_could_not_start')
        report['status'] = 'blocked_missing_runtime' if blocked else 'failed'
        report['error'] = str(exc)
        print(f'NOT VERIFIED: {exc}', file=sys.stderr)
    finally:
        report['finished_at'] = utc_now()
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
        print(f'Actual local record: {out / "result.json"}')
    if code == 0:
        print('Local Lean build, exact types, and axiom gate passed; no official or independent certification.')
    return code


if __name__ == '__main__':
    raise SystemExit(main())
