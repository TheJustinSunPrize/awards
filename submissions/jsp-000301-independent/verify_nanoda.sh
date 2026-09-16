#!/usr/bin/env bash
set -euo pipefail

# Independent rechecking for JSP-000301. Usage:
#   bash verify_nanoda.sh [path/to/JSP301-project]
# Existing matching tools may be supplied by absolute path in NANODA_BIN and
# LEAN4EXPORT_BIN. Otherwise this script builds the pinned sources below.
# Requirements: Bash, Python 3, Git, Lean/lake 4.34.0, the project's already
# built pinned dependencies, and Rust/Cargo when building Nanoda.
# This script does NOT implement the prize's full isolation/source-only policy,
# act as a designated verifier, or determine priority/award eligibility.
# No historical evidence is overwritten. All generated files go into a fresh
# temporary directory whose location is printed. Keep it to preserve the run.

exporter_commit=076e8e57707e813375e8f9da8bf989799ace9680
nanoda_commit=4c544ed4099c8227f07d5de77ad1e69fb0740a27
# Sources and licenses: both projects are Apache-2.0.
# https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680
# https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27
# The export is derived from Lean/mathlib and retains the applicable upstream
# licenses; the submitter's proof license does not relicense these dependencies.

script_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
project_dir="$(cd -- "${1:-$script_dir}" && pwd)"
runtime_dir="$(mktemp -d "${TMPDIR:-/tmp}/jsp301-nanoda.XXXXXX")"
printf 'Runtime evidence directory: %s\n' "$runtime_dir"
trap 'run_status=$?; if [ "$run_status" -ne 0 ]; then printf "Verification stopped with exit %s. Logs remain in: %s\\n" "$run_status" "$runtime_dir" >&2; fi' EXIT
mkdir "$runtime_dir/proof"
cp "$project_dir/JSP301.lean" "$runtime_dir/proof/JSP301.lean"

python3 - "$runtime_dir" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
actual = hashlib.sha256((root / "proof/JSP301.lean").read_bytes()).hexdigest()
expected = "a8dc2c9c9e2220bc2da10ae9acbaf4dee0933c59ef3e41ba6f778e9a36c9ccc7"
if actual != expected:
    raise SystemExit(f"Proof source SHA-256 mismatch: expected {expected}, got {actual}")
config = {
    "export_file_path": "JSP301.ndjson",
    "use_stdin": False,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": True,
    "unsafe_permit_all_axioms": False,
    "nat_extension": True,
    "string_extension": True,
    "num_threads": 4,
    "pp_declars": ["JSP000301.Powerful", "JSP000301.counterexample", "JSP000301.claim_false"],
    "unknown_pp_declar_hard_error": True,
    "pp_to_stdout": True,
    "pp_options": {"proofs": False, "width": 100},
    "print_success_message": True,
    "print_axioms": True,
}
(root / "nanoda-config.json").write_text(json.dumps(config, indent=2) + "\n")
PY

exporter_origin=supplied_binary_provenance_not_automatically_verified
if [ -z "${LEAN4EXPORT_BIN:-}" ]; then
  git clone --quiet https://github.com/leanprover/lean4export.git "$runtime_dir/lean4export"
  git -C "$runtime_dir/lean4export" checkout --quiet --detach "$exporter_commit"
  (cd "$runtime_dir/lean4export" && lake build) > "$runtime_dir/exporter-build.log" 2>&1
  LEAN4EXPORT_BIN="$runtime_dir/lean4export/.lake/build/bin/lean4export"
  exporter_origin=built_from_pinned_unmodified_source
fi

nanoda_origin=supplied_binary_provenance_not_automatically_verified
if [ -z "${NANODA_BIN:-}" ]; then
  git clone --quiet https://github.com/ammkrn/nanoda_lib.git "$runtime_dir/nanoda"
  git -C "$runtime_dir/nanoda" checkout --quiet --detach "$nanoda_commit"
  (cd "$runtime_dir/nanoda" && CARGO_PROFILE_RELEASE_STRIP=none cargo build --release --locked) > "$runtime_dir/nanoda-build.log" 2>&1
  NANODA_BIN="$runtime_dir/nanoda/target/release/nanoda_bin"
  nanoda_origin=built_from_pinned_unmodified_source
fi
for tool_path in "$LEAN4EXPORT_BIN" "$NANODA_BIN"; do
  case "$tool_path" in /*) ;; *) printf 'Tool paths must be absolute: %s\n' "$tool_path" >&2; exit 2 ;; esac
  test -x "$tool_path" || { printf 'Tool is not executable: %s\n' "$tool_path" >&2; exit 2; }
done

# Compile the copied source into a new target. Its directory is then placed
# FIRST in LEAN_PATH, so the exporter cannot select a stale project JSP301.olean.
# Existing dependency artifacts are reused and are NOT claimed to be source-only.
(
  cd "$project_dir"
  lake env bash -c '
    set -euo pipefail
    run_dir=$1
    export_bin=$2
    lean --version > "$run_dir/lean-version.log"
    test "$(lean --short-version)" = "4.34.0" || { echo "Lean 4.34.0 is required" >&2; exit 2; }
    if lean --root="$run_dir/proof" -o "$run_dir/proof/JSP301.olean" "$run_dir/proof/JSP301.lean" > "$run_dir/fresh-compile.log" 2>&1; then
      printf "0\n" > "$run_dir/fresh-compile.exit-code"
    else
      compile_status=$?
      printf "%s\n" "$compile_status" > "$run_dir/fresh-compile.exit-code"
      exit "$compile_status"
    fi
    if LEAN_PATH="$run_dir/proof:${LEAN_PATH:-}" "$export_bin" JSP301 -- JSP000301.claim_false JSP000301.counterexample > "$run_dir/JSP301.ndjson" 2> "$run_dir/export.log"; then
      printf "0\n" > "$run_dir/export.exit-code"
    else
      export_status=$?
      printf "%s\n" "$export_status" > "$run_dir/export.exit-code"
      exit "$export_status"
    fi
  ' _ "$runtime_dir" "$LEAN4EXPORT_BIN"
) > "$runtime_dir/compile-export-stage.log" 2>&1

if (cd "$runtime_dir" && "$NANODA_BIN" nanoda-config.json) > "$runtime_dir/nanoda-check.log" 2>&1; then
  checker_status=0
else
  checker_status=$?
fi
printf '%s\n' "$checker_status" > "$runtime_dir/nanoda.exit-code"
cat "$runtime_dir/nanoda-check.log"

python3 - "$runtime_dir" "$LEAN4EXPORT_BIN" "$NANODA_BIN" "$exporter_origin" "$nanoda_origin" <<'PY'
import datetime, hashlib, json, pathlib, platform, sys
root = pathlib.Path(sys.argv[1])
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
record = {
    "completed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "platform": platform.system(),
    "arch": platform.machine(),
    "expected_exporter_commit": "076e8e57707e813375e8f9da8bf989799ace9680",
    "expected_nanoda_commit": "4c544ed4099c8227f07d5de77ad1e69fb0740a27",
    "exporter_origin": sys.argv[4],
    "nanoda_origin": sys.argv[5],
    "exporter_binary_sha256": sha(pathlib.Path(sys.argv[2])),
    "nanoda_binary_sha256": sha(pathlib.Path(sys.argv[3])),
    "fresh_compile_exit_code": int((root / "fresh-compile.exit-code").read_text()),
    "export_exit_code": int((root / "export.exit-code").read_text()),
    "checker_exit_code": int((root / "nanoda.exit-code").read_text()),
    "export_bytes": (root / "JSP301.ndjson").stat().st_size,
    "targets": ["JSP000301.claim_false", "JSP000301.counterexample"],
    "network_disabled": False,
    "prebuilt_dependency_artifacts_ignored": False,
    "resource_limits_applied_by_this_script": False,
    "official_designated_verifier": False,
    "sha256": {name: sha(root / name) for name in [
        "proof/JSP301.lean", "proof/JSP301.olean", "JSP301.ndjson",
        "nanoda-config.json", "nanoda-check.log"]},
}
(root / "result.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
PY
exit "$checker_status"
