"""Regression tests for the 2026-09-17 review. Network tests use mocks, not downloads.

No successful Lean compilation is inferred from any test in this file.
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
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import fetch_pnt
from lean_source import strip_comments
from preflight import config_gate, arithmetic_regression_gate, PACKAGE_NAME
from verify import verification_stages, ARITHMETIC_TARGETS, parse_axioms


class ConfigurationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
            shutil.copy2(ROOT / name, self.root / name)

    def edit_lock(self, f):
        path = self.root / 'lake-manifest.json'
        data = json.loads(path.read_text())
        f(data)
        path.write_text(json.dumps(data))

    def test_repaired_root_name(self):
        report = config_gate(self.root)
        self.assertEqual(report['name'], PACKAGE_NAME)
        self.assertEqual(len(report['dependency_revisions']), 9)

    def test_original_hyphen_name_rejected(self):
        self.edit_lock(lambda d: d.update(name='jsp000883-product-proof'))
        with self.assertRaisesRegex(ValueError, 'root names'):
            config_gate(self.root)

    def test_mismatched_lakefile_rejected(self):
        path = self.root / 'lakefile.toml'
        path.write_text(path.read_text().replace(PACKAGE_NAME, 'other_package', 1))
        with self.assertRaisesRegex(ValueError, 'root names'):
            config_gate(self.root)

    def test_wrong_toolchain_rejected(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:nightly\n')
        with self.assertRaisesRegex(ValueError, 'toolchain'):
            config_gate(self.root)

    def test_floating_dependency_rejected(self):
        self.edit_lock(lambda d: d['packages'][0].update(rev='main'))
        with self.assertRaisesRegex(ValueError, 'immutable'):
            config_gate(self.root)

    def test_duplicate_dependency_rejected(self):
        self.edit_lock(lambda d: d['packages'].append(d['packages'][0].copy()))
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            config_gate(self.root)

    def test_wrong_mathlib_rejected(self):
        def change(d):
            next(p for p in d['packages'] if p['name'] == 'mathlib')['rev'] = '0' * 40
        self.edit_lock(change)
        with self.assertRaisesRegex(ValueError, 'Mathlib'):
            config_gate(self.root)

    def test_dependency_directory_rejected(self):
        self.edit_lock(lambda d: d.update(packagesDir='../untrusted'))
        with self.assertRaisesRegex(ValueError, 'directory'):
            config_gate(self.root)


class ArithmeticRegressionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'JSP000883').mkdir()
        self.path = self.root / 'JSP000883/Arithmetic.lean'
        shutil.copy2(ROOT / 'JSP000883/Arithmetic.lean', self.path)

    def test_repaired_source_screen(self):
        self.assertIn('not_elaborated', arithmetic_regression_gate(self.root)['status'])

    def test_original_product_scope_rejected(self):
        self.path.write_text(self.path.read_text().replace(
            '∏ j ∈ Icc 1 r, (m - j)', '∏ j ∈ Icc 1 r, m - j', 1))
        with self.assertRaisesRegex(ValueError, 'unparenthesized'):
            arithmetic_regression_gate(self.root)

    def test_old_erase_api_rejected(self):
        self.path.write_text(self.path.read_text().replace('Finset.notMem_erase', 'Finset.not_mem_erase'))
        with self.assertRaisesRegex(ValueError, 'Obsolete'):
            arithmetic_regression_gate(self.root)

    def test_implicit_binder_guard_required(self):
        self.path.write_text(self.path.read_text().replace('set_option autoImplicit false', ''))
        with self.assertRaisesRegex(ValueError, 'implicit'):
            arithmetic_regression_gate(self.root)

    def test_five_products_explicitly_parenthesized(self):
        text = strip_comments(self.path.read_text())
        self.assertEqual(text.count('∏ j ∈ Icc 1 r, (m - j)'), 2)
        self.assertEqual(text.count('∏ j ∈ Icc 1 r, (m + j)'), 2)
        self.assertEqual(text.count('∏ j ∈ Icc 1 (k - 1), (m + j)'), 1)

    def test_typed_audit_exists(self):
        text = strip_comments((ROOT / 'AuditArithmetic.lean').read_text())
        self.assertEqual(text.count('example'), 5)
        for name in ARITHMETIC_TARGETS:
            self.assertIn('#print axioms ' + name, text)

    def test_arithmetic_missing_report_fails(self):
        text = '\n'.join(f"'{name}' depends on axioms: [propext]" for name in ARITHMETIC_TARGETS[:-1])
        with self.assertRaisesRegex(ValueError, 'Missing'):
            parse_axioms(text, ARITHMETIC_TARGETS)


class StageOrderTests(unittest.TestCase):
    def test_full_plan_checks_finite_before_pnt(self):
        stages = verification_stages('full')
        self.assertEqual([s['name'] for s in stages], ['arithmetic', 'finite', 'growth', 'full'])
        self.assertTrue(stages[-1]['needs_pnt'])
        self.assertFalse(any(s.get('needs_pnt') for s in stages[:-1]))

    def test_finite_does_not_need_pnt(self):
        self.assertFalse(any(s.get('needs_pnt') for s in verification_stages('finite')))

    def test_growth_is_independent_of_arithmetic(self):
        self.assertEqual([s['name'] for s in verification_stages('growth')], ['growth'])

    def test_arithmetic_has_exact_type_audit(self):
        plan = verification_stages('arithmetic')
        self.assertEqual(len(plan), 1)
        self.assertEqual(plan[0]['audit'], 'AuditArithmetic.lean')

    def test_invalid_mode_rejected(self):
        with self.assertRaises(ValueError): verification_stages('skip-proof')


class SourceFetchTests(unittest.TestCase):
    def test_correct_identity(self):
        data = b'import Mathlib\n'
        with patch.object(fetch_pnt, 'read_url', return_value=data):
            receipts = []
            got = fetch_pnt.read_verified_url('https://example.invalid/pinned', len(data),
                    fetch_pnt.git_blob(data), records=receipts)
        self.assertEqual(got, data)
        self.assertEqual(receipts[0]['status'], 'identity_match')

    def test_transient_wrong_bytes_retry_without_changing_pin(self):
        data = b'import Mathlib\n'
        with patch.object(fetch_pnt, 'read_url', side_effect=[b'bad response', data]) as reader, \
             patch.object(fetch_pnt.time, 'sleep'):
            receipts = []
            got = fetch_pnt.read_verified_url('https://example.invalid/pinned', len(data),
                    fetch_pnt.git_blob(data), records=receipts)
        self.assertEqual(got, data)
        self.assertEqual(reader.call_count, 2)
        self.assertEqual([r['status'] for r in receipts], ['identity_mismatch', 'identity_match'])
        self.assertEqual({r['expected_git_blob'] for r in receipts}, {fetch_pnt.git_blob(data)})

    def test_persistent_mismatch_is_rejected(self):
        with patch.object(fetch_pnt, 'read_url', return_value=b'bad'), \
             patch.object(fetch_pnt.time, 'sleep'):
            receipts = []
            with self.assertRaisesRegex(ValueError, 'after 3 attempts'):
                fetch_pnt.read_verified_url('https://example.invalid/pinned', 4,
                    fetch_pnt.git_blob(b'good'), records=receipts)
        self.assertEqual(len(receipts), 3)
        self.assertTrue(all(r['status'] == 'identity_mismatch' for r in receipts))

    def test_same_size_wrong_content_rejected(self):
        with patch.object(fetch_pnt, 'read_url', return_value=b'evil'):
            with self.assertRaisesRegex(ValueError, 'identity/transport'):
                fetch_pnt.read_verified_url('https://example.invalid/pinned', 4,
                    fetch_pnt.git_blob(b'good'), attempts=1)

    def test_transport_error_then_valid(self):
        data = b'valid'
        with patch.object(fetch_pnt, 'read_url', side_effect=[RuntimeError('network'), data]), \
             patch.object(fetch_pnt.time, 'sleep'):
            receipts = []
            self.assertEqual(fetch_pnt.read_verified_url('https://example.invalid/pinned', len(data),
                fetch_pnt.git_blob(data), records=receipts), data)
        self.assertEqual(receipts[0]['status'], 'transport_error')

    def test_zero_attempts_rejected(self):
        with self.assertRaises(ValueError):
            fetch_pnt.read_verified_url('https://example.invalid/pinned', 0, '0' * 40, attempts=0)

    def test_atomic_write_preserves_exact_bytes(self):
        with tempfile.TemporaryDirectory() as d:
            dest = Path(d) / 'source.lean'
            fetch_pnt.write_atomic(dest, b'old')
            fetch_pnt.write_atomic(dest, b'new\r\n')
            self.assertEqual(dest.read_bytes(), b'new\r\n')
            self.assertEqual(len(list(Path(d).iterdir())), 1)


class ExperimentSafetyTests(unittest.TestCase):
    def test_optimized_python_cannot_disable_checks(self):
        proc = subprocess.run([sys.executable, '-O', str(ROOT / 'scripts/check_products.py'),
                              '--max-k', '9'], capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('Run without -O', proc.stderr)


if __name__ == '__main__':
    unittest.main()
