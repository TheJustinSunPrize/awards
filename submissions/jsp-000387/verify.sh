#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

lake build
lake env lean -DwarningAsError=true FullField.lean
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker --fresh --verbose FullField
printf '%s\n' 'PASS: compilation, guarded axiom audit, and fresh kernel replay.'
