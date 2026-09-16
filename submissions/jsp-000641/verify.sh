#!/bin/sh
set -eu
cd "$(dirname "$0")"
LEAN_BIN="${LEAN_BIN:-lean}"
version=$("$LEAN_BIN" --version)
case "$version" in
  *"version 4.24.0,"*) ;;
  *) echo "Expected Lean 4.24.0; found: $version" >&2; exit 1 ;;
esac
printf '%s\n' "$version"
"$LEAN_BIN" -t 0 DescendingWaves.lean
