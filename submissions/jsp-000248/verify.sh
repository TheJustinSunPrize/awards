#!/bin/sh
set -eu
cd "$(dirname "$0")"

LEAN_BIN="${LEAN_BIN:-lean}"
if command -v "$LEAN_BIN" >/dev/null 2>&1; then
  echo "Found Lean: $("$LEAN_BIN" --version)"
  "$LEAN_BIN" LargestDenominator.lean
  echo "Verification successful."
else
  echo "Lean not installed in environment; skipping binary check."
fi
