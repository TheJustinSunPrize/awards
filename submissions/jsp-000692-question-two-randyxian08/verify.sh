#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
mkdir -p verification/replay
lake env lean --version | tee verification/replay/version.log
lake build 2>&1 | tee verification/replay/build.log
lake env lean Audit.lean 2>&1 | tee verification/replay/axioms.log
lake env lean JSP000692.lean 2>&1 | tee verification/replay/standalone.log
python3 verification/audit_axioms.py
