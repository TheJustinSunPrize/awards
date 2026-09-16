#!/usr/bin/env bash
# Only a successful native compiler run AND complete axiom audits can pass.
# Source scans, Python checks, and historical WASM evidence are not substitutes.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p verification
stage=initializing
status_file=verification/native-status.json
on_exit() {
  code=$?
  if [[ "$code" -ne 0 ]]; then
    printf '{"status":"NOT_VERIFIED","stage":"%s","exit_code":%s}\n' \
      "$stage" "$code" > "$status_file"
  fi
}
trap on_exit EXIT
printf '%s\n' '{"status":"NOT_VERIFIED","stage":"checks_started"}' > "$status_file"
# Discard native reports from any earlier run. Never discard historical WASM evidence.
rm -f verification/lean-axioms.json verification/lean-compile.log \
  verification/core-native-axioms.json verification/core-native-compile.log \
  verification/prime-blocks-axioms.json verification/prime-blocks-compile.log \
  verification/standalone-axioms.json verification/standalone-compile.log \
  verification/native-build.log verification/lean-version.txt \
  verification/lean-environment.txt verification/verified-source-hashes.json

stage=source_hygiene
python3 -S make_standalone.py
python3 -S audit_source.py | tee verification/source-audit.json
stage=finite_witness
python3 -S verify_witness.py --output verification/finite-witness.json

stage=toolchain
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'NOT VERIFIED: native lake is unavailable; no Mathlib compilation was performed.' \
    | tee verification/lean-environment.txt >&2
  exit 2
fi
lake env lean --version | tee verification/lean-version.txt
if ! grep -Eq 'version 4\.33\.1([ ,()]|$)' verification/lean-version.txt; then
  printf '%s\n' 'STOP: Lean version does not match lean-toolchain.' >&2
  exit 2
fi
stage=dependency_pin
if [[ ! -f lake-manifest.json ]]; then
  printf '%s\n' 'STOP: run `lake update` and `lake exe cache get` first.' >&2
  exit 2
fi
python3 -S - <<'PY'
import json
import subprocess
from pathlib import Path
pin = '0df444a360eaa60ab8c11dca51a86af692955474'
manifest = json.loads(Path('lake-manifest.json').read_text())
mathlib = [p for p in manifest['packages'] if p['name'] == 'mathlib']
if len(mathlib) != 1 or mathlib[0]['rev'] != pin:
    raise SystemExit('STOP: Mathlib manifest pin mismatch.')
repo = '.lake/packages/mathlib'
head = subprocess.check_output(['git', '-C', repo, 'rev-parse', 'HEAD'], text=True).strip()
if head != pin:
    raise SystemExit('STOP: actual Mathlib checkout does not match the pin.')
if subprocess.check_output(['git', '-C', repo, 'status', '--porcelain', '--untracked-files=no'], text=True).strip():
    raise SystemExit('STOP: Mathlib has tracked working-tree changes.')
PY

stage=arithmetic_build
lake build JSP001007.Arithmetic 2>&1 | tee -a verification/native-build.log
stage=arithmetic_compile
lake env lean JSP001007/Arithmetic.lean 2>&1 | tee verification/core-native-compile.log
stage=arithmetic_axioms
python3 -S audit_axioms.py --scope core verification/core-native-compile.log \
  | tee verification/core-native-axioms.json

# Isolate the repaired analytic/number-theoretic argument before the sieve proof.
stage=prime_blocks_build
lake build JSP001007.PrimeBlocks 2>&1 | tee -a verification/native-build.log
stage=prime_blocks_compile
lake env lean JSP001007/PrimeBlocks.lean 2>&1 | tee verification/prime-blocks-compile.log
stage=prime_blocks_axioms
python3 -S audit_axioms.py --scope primes verification/prime-blocks-compile.log \
  | tee verification/prime-blocks-axioms.json

stage=main_build
lake build JSP001007 2>&1 | tee -a verification/native-build.log
stage=main_compile
lake env lean JSP001007.lean 2>&1 | tee verification/lean-compile.log
stage=main_axioms
python3 -S audit_axioms.py --scope main verification/lean-compile.log \
  | tee verification/lean-axioms.json

# Fresh whole-source check: cannot accidentally inherit a stale local theorem .olean.
stage=standalone_compile
lake env lean JSP001007Standalone.lean 2>&1 | tee verification/standalone-compile.log
stage=standalone_axioms
python3 -S audit_axioms.py --scope all verification/standalone-compile.log \
  | tee verification/standalone-axioms.json

stage=recording_verified_sources
python3 -S - <<'PY'
import hashlib
import json
from pathlib import Path
from make_standalone import render
if Path('JSP001007Standalone.lean').read_text() != render():
    raise SystemExit('STOP: generated standalone differs from canonical modules.')
paths = ['JSP001007.lean', 'JSP001007/Arithmetic.lean', 'JSP001007/PrimeBlocks.lean',
         'JSP001007Standalone.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
hashes = {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in paths}
Path('verification/verified-source-hashes.json').write_text(json.dumps(hashes, indent=2) + '\n')
PY
printf '%s\n' '{"status":"VERIFIED","scope":"native Arithmetic, PrimeBlocks, main, and fresh standalone; all 14 distinct selected transitive axiom reports passed"}' \
  > "$status_file"
printf '%s\n' 'Native module and standalone compilation passed; all 14 selected transitive axiom reports passed.'
