#!/usr/bin/env python3
"""Unit tests of audit behavior; none of these tests is a Lean proof."""
import json
import unittest
from pathlib import Path
from audit_axioms import CORE, MAIN, PRIMES, audit
from make_standalone import render
import hashlib
from audit_source import active_code, inspect

ROOT = Path(__file__).resolve().parent

class AuditTests(unittest.TestCase):
    def setUp(self):
        self.log = (ROOT / 'verification/wasm/core-compile.log').read_text()

    def test_historical_core_log_audit(self):
        self.assertEqual(set(audit(self.log, CORE, True)['reports']), CORE)

    def test_fails_if_compiler_status_missing(self):
        log = '\n'.join(l for l in self.log.splitlines() if not l.startswith('COMPILE_STATUS '))
        with self.assertRaises(ValueError):
            audit(log, CORE, True)

    def test_fails_on_extra_axiom(self):
        # Deliberately corrupted log fixture, never presented as compiler output.
        with self.assertRaises(ValueError):
            audit(self.log.replace('[propext, Quot.sound]', '[propext, NewUnprovedAssumption]'), CORE, True)

    def test_fails_on_placeholder_axiom(self):
        with self.assertRaises(ValueError):
            audit(self.log.replace('Quot.sound', 'sorryAx'), CORE, True)

    def test_fails_on_error_diagnostic(self):
        with self.assertRaises(ValueError):
            audit(self.log + '\n' + json.dumps({'severity': 'error', 'data': 'test fixture'}), CORE, True)

    def test_fails_on_missing_report(self):
        first = sorted(CORE)[0]
        with self.assertRaises(ValueError):
            audit(self.log.replace(first, 'RemovedReport'), CORE, True)

    def test_fails_on_duplicate_report(self):
        with self.assertRaises(ValueError):
            audit(self.log + "\n'JSP001007.Arithmetic.window_density' depends on axioms: []", CORE, True)

    def test_source_hygiene(self):
        for relative in ['JSP001007.lean', 'JSP001007/Arithmetic.lean', 'JSP001007/PrimeBlocks.lean', 'JSP001007Standalone.lean']:
            self.assertTrue(inspect(ROOT / relative)['passed'])

    def test_nested_comment_masking(self):
        text = '/- outer /- sorry -/ admit -/\ntheorem x : True := by trivial -- axiom\n'
        code = active_code(text)
        self.assertNotIn('sorry', code)
        self.assertNotIn('admit', code)
        self.assertIn('theorem x', code)

    def test_exact_arithmetic_body(self):
        core = (ROOT / 'JSP001007/Arithmetic.lean').read_text()
        checked = (ROOT / 'verification/wasm/CheckedArithmetic.lean.txt').read_text()
        self.assertEqual(core.removeprefix('import Lean\n'),
                         checked.removeprefix('import GameServer.Tactic.Visual\nimport Game.Browser.Runtime\n'))

    def test_standalone_is_exactly_generated(self):
        self.assertEqual((ROOT / 'JSP001007Standalone.lean').read_text(), render())

    def test_arithmetic_file_unchanged_from_original(self):
        self.assertEqual(hashlib.sha256((ROOT / 'JSP001007/Arithmetic.lean').read_bytes()).hexdigest(),
            '4171b188e090c7e75e3e77a1f4dd155e7d5824fa235256f6c1f46f49b658b304')

    def test_axiom_scopes_do_not_overlap(self):
        self.assertEqual(len(CORE | MAIN | PRIMES), 14)
        self.assertFalse(CORE & MAIN or CORE & PRIMES or MAIN & PRIMES)

if __name__ == '__main__':
    unittest.main(verbosity=2)
