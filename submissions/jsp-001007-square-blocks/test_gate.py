#!/usr/bin/env python3
"""Negative control-flow tests for run_checks.sh; NOT Lean verification.

Native commands and the finite-witness gate are mocked.
The fake lake executable below emits clearly marked synthetic report fixtures
in TemporaryDirectory instances only. Every scenario must end NOT_VERIFIED.
No synthetic compiler logs are saved in the delivery's verification directory.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'

FAKE_LAKE = r'''
import os
import sys
from pathlib import Path
sys.path.insert(0, os.getcwd())
from audit_axioms import CORE, MAIN, PRIMES
args = sys.argv[1:]
mode = os.environ['JSP_GATE_NEGATIVE_FIXTURE']
print('TEST_FIXTURE_ONLY: this executable is NOT Lean', flush=True)
with open('fixture-invocations.txt', 'a') as out:
    out.write(' '.join(args) + '\n')
if args == ['env', 'lean', '--version']:
    print('Lean (version 4.33.1, TEST_FIXTURE_ONLY)')
    sys.exit(0)
if args[0] == 'build':
    if mode == 'prime_build_failure' and args[1] == 'JSP001007.PrimeBlocks':
        print('error: synthetic build failure')
        sys.exit(1)
    sys.exit(0)
name = Path(args[-1]).name
names = {'Arithmetic.lean': CORE, 'PrimeBlocks.lean': PRIMES,
         'JSP001007.lean': MAIN, 'JSP001007Standalone.lean': CORE | MAIN | PRIMES}[name]
if mode == 'missing_prime_report' and name == 'PrimeBlocks.lean':
    names = set(sorted(names)[1:])
for n in sorted(names):
    ax = 'sorryAx' if mode == 'prime_sorry' and name == 'PrimeBlocks.lean' else 'propext, Classical.choice, Quot.sound'
    print(f"'{n}' depends on axioms: [{ax}]")
if mode == 'main_nonzero_exit' and name == 'JSP001007.lean':
    sys.exit(1)
if mode == 'standalone_error' and name == 'JSP001007Standalone.lean':
    print('error: synthetic standalone failure')
    sys.exit(1)
'''

class NativeGateNegativeTests(unittest.TestCase):
    def run_fixture(self, mode: str, expected_stage: str) -> None:
        with tempfile.TemporaryDirectory(prefix='jsp001007-negative-gate-') as td:
            work = Path(td) / 'fixture-project'
            shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns(
                '.lake', '__pycache__', '*.zip', 'reference', 'changes.patch'))
            # Test only gate control flow; do not rerun the expensive, unchanged
            # numerical verifier for every synthetic compiler failure.
            (work / 'verify_witness.py').write_text(
                'import json, sys\nfrom pathlib import Path\n'
                'Path(sys.argv[sys.argv.index("--output") + 1]).write_text('
                'json.dumps({"status": "TEST_FIXTURE_ONLY_NOT_A_NUMERICAL_CHECK"}))\n')
            (work / 'lake-manifest.json').write_text(json.dumps({
                'packages': [{'name': 'mathlib', 'rev': PIN}]}))
            fakebin = Path(td) / 'bin'
            fakebin.mkdir()
            lake = fakebin / 'lake'
            lake.write_text(f'#!{sys.executable} -S\n' + FAKE_LAKE)
            lake.chmod(0o755)
            git = fakebin / 'git'
            git.write_text(f'#!{sys.executable} -S\nimport sys\n'
                           f'if "rev-parse" in sys.argv: print({PIN!r})\n')
            git.chmod(0o755)
            # A stale success marker must be discarded before any operation.
            (work / 'verification/native-status.json').write_text('{"status":"VERIFIED"}')
            env = dict(os.environ, PATH=str(fakebin) + os.pathsep + os.environ['PATH'],
                       JSP_GATE_NEGATIVE_FIXTURE=mode)
            result = subprocess.run(['bash', 'run_checks.sh'], cwd=work, env=env,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=35)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            status = json.loads((work / 'verification/native-status.json').read_text())
            self.assertEqual(status['status'], 'NOT_VERIFIED', result.stdout)
            self.assertEqual(status['stage'], expected_stage, result.stdout)
            self.assertFalse((work / 'verification/verified-source-hashes.json').exists())
            if expected_stage.startswith('prime_blocks'):
                calls = (work / 'fixture-invocations.txt').read_text().splitlines()
                self.assertNotIn('env lean JSP001007.lean', calls)
                self.assertNotIn('env lean JSP001007Standalone.lean', calls)

    def test_build_failure_stops_before_main(self):
        self.run_fixture('prime_build_failure', 'prime_blocks_build')

    def test_zero_exit_with_sorry_axiom_is_rejected(self):
        self.run_fixture('prime_sorry', 'prime_blocks_axioms')

    def test_missing_prime_report_is_rejected(self):
        self.run_fixture('missing_prime_report', 'prime_blocks_axioms')

    def test_main_nonzero_exit_even_with_clean_reports_is_rejected(self):
        self.run_fixture('main_nonzero_exit', 'main_compile')

    def test_standalone_failure_cannot_inherit_module_success(self):
        self.run_fixture('standalone_error', 'standalone_compile')

if __name__ == '__main__':
    unittest.main(verbosity=2)
