"""Negative controls for the auxiliary transcription checker (not Lean tests)."""
from pathlib import Path
import tempfile
import unittest

from audit import EDGES, EDGE_BLUE, VERTEX_BLUE, THREE, audit
from source_audit import AuditError, audit_source, without_comments
from verify_lean import parse_axioms, TARGETS

EXPECTED = {'edges':EDGES, 'edge_blue':EDGE_BLUE, 'vertex_blue':VERTEX_BLUE, 'three':THREE}
SOURCE = Path(__file__).with_name('JSP690.lean').read_text(encoding='utf-8')


class SourceAuditTests(unittest.TestCase):
    def check_source(self, text):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'JSP690.lean'
            path.write_text(text, encoding='utf-8')
            return audit_source(path, EXPECTED)

    def test_original_and_finite_checks(self):
        self.assertEqual(audit()['proper_binary_colorings'], 0)

    def test_reject_changed_edge(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('⟨0, 1, 2, by decide, by decide⟩',
                                             '⟨0, 1, 3, by decide, by decide⟩', 1))

    def test_reject_changed_obstruction(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('(x0 ≠ x1 ∨ x0 ≠ x2)',
                                             '(x0 ≠ x1 ∨ x0 ≠ x3)', 1))

    def test_reject_changed_edge_certificate(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('| 0, 1, 2 => [5, 6, 7, 8]',
                                             '| 0, 1, 2 => [4, 6, 7, 8]', 1))

    def test_reject_changed_vertex_certificate(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('| 0 => [1, 2, 3, 4]',
                                             '| 0 => [1, 2, 3, 5]', 1))

    def test_reject_sorry(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('by decide', 'by sorry', 1))

    def test_reject_new_axiom(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE + '\naxiom fake : False\n')

    def test_reject_native_decide(self):
        with self.assertRaises(AuditError):
            self.check_source(SOURCE.replace('by decide', 'by native_decide', 1))

    def test_comment_stripping(self):
        self.assertEqual(without_comments('a /- nested /- text -/ x -/ b -- end\nc').split(),
                         ['a', 'b', 'c'])

    def test_missing_axiom_output_is_not_success(self):
        with self.assertRaises(RuntimeError):
            parse_axioms('')

    def test_sorry_axiom_output_is_rejected(self):
        synthetic = '\n'.join(
            f"'{name}' depends on axioms: [sorryAx]" for name in TARGETS)
        with self.assertRaises(RuntimeError):
            parse_axioms(synthetic)


if __name__ == '__main__':
    unittest.main()
