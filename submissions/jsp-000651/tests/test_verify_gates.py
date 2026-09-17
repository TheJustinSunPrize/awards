"""Black-box regression: optimized Python must never report failed checks as pass.

The temporary Lake stub simulates failures; these tests do not certify Lean.
The real proof checks are performed separately by verify.py with the real Lake.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
LAKE_STUB = r'''
import os, sys
from pathlib import Path
mode = os.environ["VERIFIER_GATE_TEST"]
args = sys.argv[1:]
if args == ["env", "lean", "--version"]:
    print("Lean (version " + ("0.0.0" if mode == "version" else "4.34.0") + ", stub)")
elif args == ["build"]:
    sys.exit(1 if mode == "build" else 0)
elif args and args[-1] == "Audit.lean":
    if mode == "audit_exit": sys.exit(1)
    names = ['middle_card', 'middle_sumFree', 'middle_third_nonzero', 'erdos_lower_bound', 'singleton_zero_exception']
    if mode == "audit_missing": names.pop()
    axioms = "unexpected_axiom" if mode == "audit_axiom" else "propext, Classical.choice, Quot.sound"
    for name in names:
        print("'SumFreeBound." + name + "' depends on axioms: [" + axioms + "]")
elif "leanchecker" in args:
    sys.exit(1 if mode == "replay" else 0)
else:
    name = Path(args[-1]).stem
    if name == "custom_axiom":
        if mode == "custom_exit": sys.exit(1)
        axiom = "propext" if mode == "custom_unflagged" else "unexpected_axiom"
        print("'contaminated' depends on axioms: [" + axiom + "]")
    elif name in ("false_arithmetic", "placeholder"):
        sys.exit(0 if mode == name else 1)
    else:
        raise RuntimeError("Unexpected stub command: " + repr(args))
'''


class OptimizedVerifierGates(unittest.TestCase):
    def run_case(self, mode):
        with tempfile.TemporaryDirectory(prefix="gate-regression-", dir=ROOT) as temp:
            fixture = Path(temp)
            shutil.copyfile(ROOT / "verify.py", fixture / "verify.py")
            for name in ("SumFreeBound.lean", "Audit.lean",
                         "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                target = fixture / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("axiom bad : False\n" if mode == "source" and
                                  name == "SumFreeBound.lean" else "\n")
            bindir = fixture / "bin"
            bindir.mkdir()
            stub = bindir / "lake"
            stub.write_text("#!" + sys.executable + "\n" + LAKE_STUB)
            stub.chmod(0o700)
            env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ.get("PATH", ""),
                       VERIFIER_GATE_TEST=mode)
            proc = subprocess.run([sys.executable, "-O", "verify.py"], cwd=fixture,
                                  env=env, capture_output=True, text=True)
            receipt_path = fixture / "evidence/verification.json"
            receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else None
            return proc, receipt

    def test_optimized_success_control(self):
        proc, receipt = self.run_case("success")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(receipt["local_validation"], "pass")
        self.assertEqual(receipt["python_optimization_level"], 1)

    def test_optimized_failures_do_not_write_success(self):
        for mode in ("source", "version", "build", "audit_exit", "audit_missing", "audit_axiom",
                     "false_arithmetic", "placeholder", "custom_exit", "custom_unflagged", "replay"):
            with self.subTest(mode=mode):
                proc, receipt = self.run_case(mode)
                self.assertNotEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assertIn("Verification failed:", proc.stderr)
                self.assertIsNone(receipt)


if __name__ == "__main__":
    unittest.main()
