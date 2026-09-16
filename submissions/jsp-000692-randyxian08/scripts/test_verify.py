"""Unit tests of the utility's report parser, not of any Lean theorem."""
import unittest
from verify import parse_axioms, VerificationError
from source_audit import strip_comments_and_strings, FORBIDDEN


class AuditParserTests(unittest.TestCase):
    def test_standard_report(self):
        result = parse_axioms("'JSP692.t' depends on axioms: [propext, Classical.choice, Quot.sound]", ['JSP692.t'])
        self.assertEqual(set(result['JSP692.t']), {'propext', 'Classical.choice', 'Quot.sound'})

    def test_multiline_report(self):
        result = parse_axioms("JSP692.t depends on axioms:\n[propext,\n Quot.sound]", ['JSP692.t'])
        self.assertEqual(set(result['JSP692.t']), {'propext', 'Quot.sound'})

    def test_empty_report(self):
        self.assertEqual(parse_axioms("'JSP692.t' does not depend on any axioms", ['JSP692.t']), {'JSP692.t': []})

    def test_missing_report_is_failure(self):
        with self.assertRaises(VerificationError):
            parse_axioms("Build completed successfully.", ['JSP692.t'])

    def test_sorry_axiom_is_failure(self):
        with self.assertRaises(VerificationError):
            parse_axioms("'JSP692.t' depends on axioms: [propext, sorryAx]", ['JSP692.t'])

    def test_new_axiom_is_failure(self):
        with self.assertRaises(VerificationError):
            parse_axioms("'JSP692.t' depends on axioms: [JSP692.assumed_bound]", ['JSP692.t'])

    def test_missing_second_theorem_is_failure(self):
        with self.assertRaises(VerificationError):
            parse_axioms("'JSP692.t' depends on axioms: [propext]", ['JSP692.t', 'JSP692.u'])


class SourceScannerTests(unittest.TestCase):
    def test_nested_comments_are_removed(self):
        code = strip_comments_and_strings('/- sorry /- axiom -/ -/ theorem t : True := by trivial')
        self.assertIsNone(FORBIDDEN.search(code))

    def test_uncommented_placeholder_is_detected(self):
        code = strip_comments_and_strings('theorem t : True := by sorry -- not permitted')
        self.assertIsNotNone(FORBIDDEN.search(code))

    def test_unterminated_comment_is_failure(self):
        with self.assertRaises(ValueError):
            strip_comments_and_strings('/- unfinished')

    def test_strings_are_not_proofs(self):
        code = strip_comments_and_strings('def s := "sorry"')
        self.assertIsNone(FORBIDDEN.search(code))


if __name__ == '__main__':
    unittest.main()
