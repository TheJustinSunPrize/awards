"""Regression checks for verification gates, not mathematical proof tests."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import bootstrap
from verify import DECLARATIONS, audit_axioms


def audit_output(extra: str = "") -> str:
    return "\n".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound{extra}]"
        for name in DECLARATIONS
    )


class VerificationGates(unittest.TestCase):
    def test_standard_axioms_accepted(self):
        self.assertEqual(set(audit_axioms(audit_output())), set(DECLARATIONS))

    def test_unsafe_and_custom_axioms_rejected(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "AssumedPNT"):
            with self.subTest(axiom=axiom), self.assertRaisesRegex(RuntimeError, "Unexpected"):
                audit_axioms(audit_output(", " + axiom))

    def test_missing_declaration_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Missing"):
            audit_axioms(audit_output().splitlines()[0])

    def test_altered_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "Proof.lean"
            source.write_text("original source", encoding="utf-8")
            lock = root / "lock.json"
            lock.write_text(json.dumps({"sources": {"Proof.lean": bootstrap.digest(source)}}))
            with patch.object(bootstrap, "ROOT", root), patch.object(bootstrap, "LOCK", lock):
                bootstrap.verify_sources()
                source.write_text("modified source", encoding="utf-8")
                with self.assertRaisesRegex(RuntimeError, "checksum mismatch"):
                    bootstrap.verify_sources()

    def test_cache_path_escape_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            bootstrap.within_root("../../outside.lean")


if __name__ == "__main__":
    unittest.main()
