"""Infrastructure and finite arithmetic tests; no test here runs Lean."""
from __future__ import annotations
import json
import math
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from lean_source import strip_comments, imports
from verify import source_gate, parse_axioms, run_command
from fetch_pnt import git_blob
from check_products import check_pair


class SourceAndGateTests(unittest.TestCase):
    def test_nested_comments(self):
        s = 'theorem a : True := by /- sorry /- axiom X -/ -/ trivial'
        self.assertNotIn('sorry', strip_comments(s))
        self.assertIn('trivial', strip_comments(s))

    def test_string_not_code(self):
        self.assertNotIn('sorry', strip_comments('def label := "sorry -- /-"'))

    def test_line_comments(self):
        self.assertEqual(strip_comments('-- sorry\nx').splitlines()[-1], 'x')

    def test_unterminated_comment_fails(self):
        with self.assertRaises(ValueError): strip_comments('/- unfinished')

    def test_import_parser(self):
        self.assertEqual(imports('module\npublic import Mathlib.Data.Nat.Basic\nimport Foo.Bar Baz\n'),
                         ['Mathlib.Data.Nat.Basic', 'Foo.Bar', 'Baz'])

    def test_fake_import_in_comment_ignored(self):
        self.assertEqual(imports('/- import Bad -/\nimport Good\n'), ['Good'])

    def test_source_gate_real_package(self):
        r = source_gate(ROOT)
        self.assertGreater(sum(x['theorem_or_lemma_declarations'] for x in r['files']), 30)

    def test_definition_only_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            shutil.copytree(ROOT/'JSP000883', root/'JSP000883')
            p = root/'JSP000883/FiniteConstruction.lean'
            p.write_text('import JSP000883.Targets\nnamespace JSP000883\ndef finiteConstruction : Prop := FiniteConstructionClaim\nend JSP000883\n')
            with self.assertRaisesRegex(ValueError, 'Proof declarations missing'):
                source_gate(root)

    def test_placeholder_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            shutil.copytree(ROOT/'JSP000883', root/'JSP000883')
            p = root/'JSP000883/Growth.lean'
            p.write_text(p.read_text()+'\ntheorem unacceptable : False := by sorry\n')
            with self.assertRaisesRegex(ValueError, 'Forbidden source token'):
                source_gate(root)

    def test_standard_axioms(self):
        s = "'X' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(len(parse_axioms(s, ['X'])['X']), 3)

    def test_multiline_axioms(self):
        s = "'X' depends on axioms:\n [propext,\n Quot.sound]\n"
        self.assertEqual(parse_axioms(s, ['X'])['X'], ['propext','Quot.sound'])

    def test_sorry_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError,'Unapproved'):
            parse_axioms("'X' depends on axioms: [sorryAx]", ['X'])

    def test_custom_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError,'Unapproved'):
            parse_axioms("'X' depends on axioms: [Hypothesis.PNT]", ['X'])

    def test_missing_audit_rejected(self):
        with self.assertRaisesRegex(ValueError,'Missing'):
            parse_axioms('Build completed successfully', ['X'])

    def test_duplicate_audit_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate'):
            parse_axioms("'X' depends on axioms: []\n'X' depends on axioms: []", ['X'])

    def test_missing_executable_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            records = []
            with self.assertRaises(RuntimeError):
                run_command(['/definitely-not-a-real-program-jsp883'],Path(d)/'out.log',records)
            self.assertFalse(records[0]['executed'])
            self.assertIsNone(records[0]['exit_code'])

    def test_nonzero_process_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            records=[]
            with self.assertRaises(RuntimeError):
                run_command([sys.executable,'-c','raise SystemExit(7)'],Path(d)/'out.log',records)
            self.assertEqual(records[0]['exit_code'],7)

    def test_git_blob_hash(self):
        self.assertEqual(git_blob(b''),'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391')

    def test_locked_mathlib(self):
        data=json.loads((ROOT/'lake-manifest.json').read_text())
        entry=next(p for p in data['packages'] if p['name']=='mathlib')
        self.assertEqual(entry['rev'],'db584cd6d46c92f209a44c0f1c829460d327499d')


class ProductTests(unittest.TestCase):
    def test_left(self):
        r=check_pair(9,5)
        self.assertFalse(r['right']); self.assertEqual(r['offset'],0)

    def test_right(self):
        r=check_pair(22,13)
        self.assertTrue(r['right']); self.assertEqual(r['offset'],21)

    def test_invalid_input(self):
        with self.assertRaises(ValueError): check_pair(16,9)

    def test_abstract_cancellation(self):
        for p in (2,3,5,7):
            for f in range(1,8):
                q=[p,2*p,3,4]
                B=f*math.prod(q)//p
                self.assertEqual(B%f,0)
                self.assertTrue(all(B%x==0 for x in q))

    def test_single_multiple_is_not_enough(self):
        p=5; q=[5,2]; f=1
        B=f*math.prod(q)//p
        self.assertNotEqual(B%q[0],0)


if __name__ == '__main__': unittest.main()
