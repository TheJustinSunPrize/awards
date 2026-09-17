#!/usr/bin/env python3
"""Unit tests of tooling with synthetic input; NOT mathematical verification."""
import unittest
import hashlib

from common import forbidden_constructs, imported_modules, strip_comments_and_strings
from check_axioms import EXPECTED, parse_and_validate
from fetch_upstream import git_blob_sha1, validate_identity


class ToolingTests(unittest.TestCase):
    def test_corrupt_source_and_truncated_response_are_rejected(self):
        source = b'theorem checked : True := by trivial\n'
        expected = {'path': 'test.lean', 'bytes': len(source),
                    'sha256': hashlib.sha256(source).hexdigest(),
                    'git_blob_sha1': git_blob_sha1(source)}
        validate_identity(source, expected)
        for changed in (source[:-1], source.replace(b'True', b'true')):
            with self.subTest(data=changed), self.assertRaises(RuntimeError):
                validate_identity(changed, expected)

    def test_nested_comments_are_not_proof_holes(self):
        source = '/- sorry /- admit -/ axiom -/\n theorem t : True := by trivial\n'
        self.assertEqual(forbidden_constructs(source), [])

    def test_real_proof_hole_is_detected(self):
        self.assertEqual(forbidden_constructs('theorem t : True := by sorry'), ['sorry'])

    def test_print_axioms_is_allowed(self):
        self.assertEqual(forbidden_constructs('#print axioms Foo.bar'), [])

    def test_imports(self):
        source = '/- import Hidden -/\npublic import Mathlib.A\nimport ErdosProblems.B\n'
        self.assertEqual(imported_modules(source), ['Mathlib.A', 'ErdosProblems.B'])

    def test_malformed_comments(self):
        with self.assertRaises(ValueError):
            strip_comments_and_strings('/- unfinished')

    @staticmethod
    def synthetic_log(axioms='propext, Classical.choice, Quot.sound'):
        return '\n'.join(f"'{name}' depends on axioms: [{axioms}]" for name in EXPECTED)

    def test_synthetic_allowed_audit(self):
        self.assertEqual(len(parse_and_validate(self.synthetic_log())), len(EXPECTED))

    def test_synthetic_custom_axiom_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_and_validate(self.synthetic_log('propext, UnprovedFiniteTheorem'))

    def test_synthetic_sorry_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_and_validate(self.synthetic_log('sorryAx'))

    def test_incomplete_audit_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_and_validate("'JSP000078.erdos_58_exact_statement' depends on axioms: [propext]")

    def test_synthetic_empty_audit(self):
        log = '\n'.join(f"'{name}' does not depend on any axioms" for name in EXPECTED)
        self.assertEqual(parse_and_validate(log), {name: [] for name in EXPECTED})


if __name__ == '__main__':
    unittest.main(verbosity=2)
