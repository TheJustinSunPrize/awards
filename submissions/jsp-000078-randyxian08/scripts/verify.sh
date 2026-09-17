#!/usr/bin/env bash
# Execute in the user's environment. No build result is pre-recorded in this bundle.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
rm -f verification/BUILD_AND_AUDIT_PASSED verification/axioms.actual.json verification/replay.actual.json

command -v python3 >/dev/null || { echo 'python3 is required.' >&2; exit 1; }
command -v lake >/dev/null || {
  echo 'Lean/Lake is missing. Install elan, then run this script again.' >&2
  echo 'No build or axiom verification has been performed.' >&2
  exit 1
}
command -v git >/dev/null || { echo 'git is required.' >&2; exit 1; }

python3 scripts/static_check.py | tee verification/static.actual.log
python3 scripts/fetch_upstream.py | tee verification/fetch.actual.log
lake update 2>&1 | tee verification/dependencies.actual.log
lake env lean --version 2>&1 | tee verification/lean-version.actual.log
grep -q '4.33.0' verification/lean-version.actual.log || {
  echo 'Unexpected Lean version; stopped.' >&2; exit 1;
}
ACTUAL_MATHLIB=$(git -C .lake/packages/mathlib rev-parse HEAD)
test "$ACTUAL_MATHLIB" = db584cd6d46c92f209a44c0f1c829460d327499d || {
  echo 'Mathlib commit mismatch; stopped.' >&2; exit 1;
}
lake exe cache get 2>&1 | tee verification/cache.actual.log

# Build stages are separated so an upstream failure is not mistaken for a
# failure in the new compactness proof, or vice versa.
lake build JSP000078.Compactness 2>&1 | tee verification/compactness.actual.log
lake build ErdosProblems.Erdos58 2>&1 | tee verification/finite-proof.actual.log
lake build JSP000078 2>&1 | tee verification/general-proof.actual.log
lake env lean JSP000078/Audit.lean 2>&1 | tee verification/axioms.actual.log
python3 scripts/check_axioms.py verification/axioms.actual.log \
  --json-output verification/axioms.actual.json
python3 scripts/replay.py
printf '%s\n' 'Build commands, transitive axiom audit and project kernel replay completed successfully.' \
  > verification/BUILD_AND_AUDIT_PASSED
printf '\n%s\n' 'BUILD AND AXIOM AUDIT PASSED IN THIS RUN.'
printf '%s\n' 'This is not a prize-eligibility, priority, or committee acceptance decision.'
