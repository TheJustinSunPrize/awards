"""Adversarial security tests for audit.py verification pipeline."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "audit.py"
spec = importlib.util.spec_from_file_location("lean_audit", SCRIPT)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def manifest(root, targets=None, sha="a" * 40, toolchain="leanprover/lean4:v4.32.0"):
    targets = targets or [{"id": "main", "problem": "fixture", "role": "theorem",
                           "module": "Fixture", "source": "Fixture.lean", "declaration": "Fixture.good"}]
    return {"schema_version": 1,
            "project": {"root": str(root), "repository": "local-fixture", "commit": sha, "toolchain": toolchain},
            "problems": [{"id": "fixture", "source": "test fixture",
                          "requirements": [{"id": "main", "description": "test",
                                            "targets": [t["id"] for t in targets], "coverage": "pending"}]}],
            "targets": targets}


class AdversarialSecurityTests(unittest.TestCase):
    """Security-focused adversarial tests."""
    
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="lean-audit-adversarial-")
        self.root = Path(self.tmp.name) / "project"
        self.root.mkdir()
        self.file = Path(self.tmp.name) / "targets.json"
    
    def tearDown(self):
        self.tmp.cleanup()
    
    def load(self, data):
        self.file.write_text(json.dumps(data))
        return audit.load_manifest(self.file)
    
    def test_command_injection_via_module_name(self):
        """Module names cannot inject shell commands."""
        data = manifest(self.root)
        data["targets"][0]["module"] = "Fixture; rm -rf /"
        with self.assertRaises(ValueError):
            self.load(data)
    
    def test_command_injection_via_declaration_name(self):
        """Declaration names cannot inject shell commands."""
        data = manifest(self.root)
        data["targets"][0]["declaration"] = "good`$(whoami)`"
        with self.assertRaises(ValueError):
            self.load(data)
    
    def test_path_traversal_via_source(self):
        """Source paths cannot traverse outside project."""
        data = manifest(self.root)
        data["targets"][0]["source"] = "../../etc/passwd"
        with self.assertRaises(ValueError):
            self.load(data)
    
    def test_absolute_path_in_source_rejected(self):
        """Absolute source paths are rejected."""
        data = manifest(self.root)
        data["targets"][0]["source"] = "/tmp/malicious.lean"
        with self.assertRaises(ValueError):
            self.load(data)
    
    def test_symlink_escape_detected(self):
        """Symlinks escaping project root are rejected."""
        outside = Path(self.tmp.name) / "outside.lean"
        outside.write_text("axiom pwned : False\n")
        (self.root / "Evil.lean").symlink_to(outside)
        data = manifest(self.root)
        data["targets"][0]["source"] = "Evil.lean"
        with self.assertRaises(ValueError):
            self.load(data)
    
    def test_lockfile_with_short_sha_rejected(self):
        """Short Git SHAs (7 chars) are rejected - must be 40 chars."""
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
        (self.root / "lakefile.lean").write_text("package fixture\n")
        (self.root / "Fixture.lean").write_text("theorem good : True := True.intro\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.1.0",
            "packages": [
                {"name": "short_sha_pkg", "git": {"url": "https://example.com/repo", "rev": "abc1234"}}
            ]
        }))
        data = manifest(self.root)
        result = audit.preflight(data, self.root)
        self.assertIn("unpinned_dependency:short_sha_pkg", result["issues"])
    
    def test_lockfile_with_branch_name_rejected(self):
        """Branch names instead of SHAs are rejected."""
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
        (self.root / "lakefile.lean").write_text("package fixture\n")
        (self.root / "Fixture.lean").write_text("theorem good : True := True.intro\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.1.0",
            "packages": [
                {"name": "branch_pkg", "git": {"url": "https://example.com/repo", "rev": "main"}}
            ]
        }))
        data = manifest(self.root)
        result = audit.preflight(data, self.root)
        self.assertIn("unpinned_dependency:branch_pkg", result["issues"])
    
    def test_lockfile_with_tag_rejected(self):
        """Git tags instead of commit SHAs are rejected."""
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
        (self.root / "lakefile.lean").write_text("package fixture\n")
        (self.root / "Fixture.lean").write_text("theorem good : True := True.intro\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.1.0",
            "packages": [
                {"name": "tag_pkg", "git": {"url": "https://example.com/repo", "rev": "v1.0.0"}}
            ]
        }))
        data = manifest(self.root)
        result = audit.preflight(data, self.root)
        self.assertIn("unpinned_dependency:tag_pkg", result["issues"])
    
    def test_sorry_in_transitive_dependency_detected(self):
        """Transitive sorry dependencies are classified as proof_gap."""
        axioms = ["propext", "Classical.choice", "Quot.sound", "sorryAx"]
        self.assertEqual(audit.classify(axioms), "proof_gap")
    
    def test_custom_axiom_flagged_for_review(self):
        """Custom axioms trigger trust_review_required."""
        axioms = ["propext", "CustomAxiom"]
        self.assertEqual(audit.classify(axioms), "trust_review_required")
    
    def test_malicious_axiom_name_with_injection(self):
        """Axiom names with shell metacharacters are rejected."""
        output = "'Fixture.good' depends on axioms: [propext, `$(rm -rf /)`]\n"
        with self.assertRaises(ValueError):
            audit.parse_axioms(output, "Fixture.good")
    
    def test_empty_lockfile_packages_array(self):
        """Empty packages array is valid but triggers no unpinned warnings."""
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
        (self.root / "lakefile.lean").write_text("package fixture\n")
        (self.root / "Fixture.lean").write_text("theorem good : True := True.intro\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "version": "1.1.0",
            "packages": []
        }))
        data = manifest(self.root)
        result = audit.preflight(data, self.root)
        # Empty array is valid, no corrupted_dependency_lock
        self.assertNotIn("corrupted_dependency_lock", result["issues"])
    
    def test_timeout_does_not_block_indefinitely(self):
        """Timeout kills process and returns within bounded time."""
        log = Path(self.tmp.name) / "timeout.log"
        import time
        start = time.time()
        result = audit.capture([sys.executable, "-c", "import time; time.sleep(1000)"],
                               self.root, log, 0.05)
        elapsed = time.time() - start
        self.assertEqual(result["status"], "timeout")
        # Should complete within 10 seconds (0.05s timeout + 5s bounded wait + overhead)
        self.assertLess(elapsed, 10.0)
    
    def test_nonexistent_binary_fails_gracefully(self):
        """Missing binary produces launch_failed, not uncaught exception."""
        log = Path(self.tmp.name) / "missing.log"
        result = audit.capture(["/nonexistent/binary/path/lean"], self.root, log, 1.0)
        self.assertEqual(result["status"], "launch_failed")
        self.assertIn("error", result)


if __name__ == "__main__":
    unittest.main()
