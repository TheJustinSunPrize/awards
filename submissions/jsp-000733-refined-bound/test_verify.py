"""Regression tests for verification records; these tests do not compile Lean."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock


SCRIPT = Path(__file__).with_name("verify.py")
spec = importlib.util.spec_from_file_location("erdos882_verify", SCRIPT)
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


class VerificationRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="erdos882-verifier-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        shutil.copy2(SCRIPT, self.root / "verify.py")
        (self.root / "logs").mkdir()
        self.old_results = b'{"run_id":"old-run","status":"PASS"}\n'
        (self.root / "logs/results.json").write_bytes(self.old_results)
        (self.root / "logs/previous.log").write_bytes(b"Original raw output.\n")
        self.env = os.environ.copy()
        self.env["PATH"] = ""

    def command(self, *arguments: str) -> list[str]:
        return [sys.executable, str(self.root / "verify.py"),
                "--no-local-toolchain", *arguments]

    def latest(self) -> dict:
        return json.loads((self.root / "logs/results.json").read_text(encoding="utf-8"))

    def check_failed_record(self, record: dict) -> None:
        self.assertEqual(record["status"], "FAIL")
        self.assertEqual(record["process_exit_code"], 1)
        self.assertNotEqual(record["run_id"], "old-run")
        self.assertLessEqual(record["started_utc"], record["finished_utc"])
        archive = Path(record["previous_logs_archive"])
        self.assertEqual(archive, self.root / ".verification-history" / record["run_id"] / "logs")
        self.assertEqual((archive / "results.json").read_bytes(), self.old_results)
        self.assertEqual((archive / "previous.log").read_bytes(), b"Original raw output.\n")
        self.assertFalse((self.root / "logs/previous.log").exists())
        self.assertEqual(list((self.root / "logs").glob(".results.json.*.tmp")), [])

    def make_fake_lake(self, *, wait_for_release: bool) -> Path:
        """Create a local launcher whose first command can be observed or timed out."""
        binary = self.root / "fake-bin"
        binary.mkdir()
        fake = binary / "fake_lake.py"
        fake.write_text(
            "from pathlib import Path\nimport time\n"
            f"root = Path({str(self.root)!r})\n"
            "(root / 'fake-started').write_text('started')\n"
            "print('fake Lake started', flush=True)\n"
            + ("deadline = time.monotonic() + 10\n"
               "while not (root / 'release').exists() and time.monotonic() < deadline:\n"
               "    time.sleep(0.01)\n" if wait_for_release else "time.sleep(0.8)\n")
            + "print('deliberately invalid Lean version', flush=True)\n",
            encoding="utf-8",
        )
        if os.name == "nt":
            launcher = binary / "lake.cmd"
            launcher.write_text(f'@echo off\n"{sys.executable}" -u "{fake}" %*\n',
                                encoding="utf-8")
        else:
            launcher = binary / "lake"
            launcher.write_text(f"#!{sys.executable}\nexec(compile(open({str(fake)!r}).read(), "
                                f"{str(fake)!r}, 'exec'))\n", encoding="utf-8")
            launcher.chmod(0o755)
        return binary

    def test_missing_lake_replaces_old_pass_and_preserves_original_logs(self) -> None:
        completed = subprocess.run(self.command(), cwd=self.root, env=self.env,
                                   text=True, capture_output=True, timeout=15)
        self.assertEqual(completed.returncode, 1, completed.stdout + completed.stderr)
        record = self.latest()
        self.check_failed_record(record)
        self.assertIn("Lake not found", record["error"])
        self.assertEqual(record["commands"], [])

    def test_running_record_is_visible_before_command_completes(self) -> None:
        binary = self.make_fake_lake(wait_for_release=True)
        process = subprocess.Popen(self.command("--lean-bin", str(binary)), cwd=self.root,
                                   env=self.env, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 8
            while not (self.root / "fake-started").exists():
                if process.poll() is not None:
                    self.fail(f"Verifier exited before fake Lake started: {process.communicate()[0]}")
                if time.monotonic() >= deadline:
                    self.fail("Fake Lake did not start")
                time.sleep(0.01)
            running = self.latest()
            self.assertEqual(running["status"], "RUNNING")
            self.assertNotEqual(running["run_id"], "old-run")
            self.assertNotIn("finished_utc", running)
            self.assertEqual(running["commands"][0]["status"], "RUNNING")
            self.assertIsNone(running["commands"][0]["exit_code"])
            self.assertIsNone(process.poll())
            (self.root / "release").touch()
            output = process.communicate(timeout=15)[0]
            self.assertEqual(process.returncode, 1, output)
            final = self.latest()
            self.check_failed_record(final)
            self.assertEqual(final["run_id"], running["run_id"])
            self.assertIn("Wrong Lean version", final["error"])
            self.assertEqual(final["commands"][0]["status"], "COMPLETED")
            self.assertEqual(final["commands"][0]["exit_code"], 0)
        finally:
            (self.root / "release").touch()
            if process.poll() is None:
                process.kill()
            process.communicate(timeout=15)

    def test_timeout_is_a_new_failed_run_with_command_evidence(self) -> None:
        binary = self.make_fake_lake(wait_for_release=False)
        completed = subprocess.run(self.command("--lean-bin", str(binary),
                                                "--command-timeout", "0.2"),
                                   cwd=self.root, env=self.env, text=True,
                                   capture_output=True, timeout=15)
        self.assertEqual(completed.returncode, 1, completed.stdout + completed.stderr)
        record = self.latest()
        self.check_failed_record(record)
        self.assertIn("TimeoutExpired", record["error"])
        command = record["commands"][0]
        self.assertEqual(command["status"], "TIMED_OUT")
        self.assertIsNone(command["exit_code"])
        self.assertEqual(command["timeout_seconds"], 0.2)
        self.assertIn("finished_utc", command)
        self.assertIn("TIMED_OUT", (self.root / "logs/lean-version.log").read_text())

    def test_command_launch_error_updates_final_and_command_records(self) -> None:
        absent_lake = self.root / "nonexistent-lake"
        with mock.patch.object(verify, "ROOT", self.root), \
                mock.patch.object(sys, "argv", self.command()[1:]), \
                mock.patch.object(verify.shutil, "which", return_value=str(absent_lake)), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            code = verify.main()
        self.assertEqual(code, 1)
        record = self.latest()
        self.check_failed_record(record)
        self.assertIn("FileNotFoundError", record["error"])
        self.assertEqual(record["commands"][0]["status"], "ERROR")
        self.assertIsNone(record["commands"][0]["exit_code"])

    def test_initialization_error_is_recorded_before_tool_discovery(self) -> None:
        completed = subprocess.run(self.command("--command-timeout", "0"), cwd=self.root,
                                   env=self.env, text=True, capture_output=True, timeout=15)
        self.assertEqual(completed.returncode, 1)
        record = self.latest()
        self.check_failed_record(record)
        self.assertIn("--command-timeout must be positive", record["error"])
        self.assertEqual(record["commands"], [])

    def test_atomic_replace_uses_complete_sibling_and_preserves_old_on_failure(self) -> None:
        destination = self.root / "logs/results.json"
        actual_replace = os.replace

        def inspect_replace(source: Path, target: Path) -> None:
            self.assertEqual(Path(source).parent, destination.parent)
            self.assertEqual(Path(target), destination)
            self.assertEqual(json.loads(Path(source).read_text()), {"status": "RUNNING"})
            self.assertEqual(destination.read_bytes(), self.old_results)
            actual_replace(source, target)

        with mock.patch.object(verify.os, "replace", side_effect=inspect_replace):
            verify.atomic_json(destination, {"status": "RUNNING"})
        self.assertEqual(json.loads(destination.read_text()), {"status": "RUNNING"})
        before = destination.read_bytes()
        with mock.patch.object(verify.os, "replace", side_effect=OSError("injected replace failure")):
            with self.assertRaisesRegex(OSError, "injected replace failure"):
                verify.atomic_json(destination, {"status": "FAIL"})
        self.assertEqual(destination.read_bytes(), before)
        self.assertEqual(list(destination.parent.glob(".results.json.*.tmp")), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
