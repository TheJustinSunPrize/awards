#!/usr/bin/env bash
set -euo pipefail
# Run from the project root. Optionally pass an already-fetched Lake packages directory.
proof_repro=$(mktemp -d)
tar --exclude=.git --exclude=.lake -cf - . | tar -xf - -C "$proof_repro"
if [ "$#" -eq 1 ]; then
  mkdir -p "$proof_repro/.lake"
  ln -s "$(realpath "$1")" "$proof_repro/.lake/packages"
fi
cd "$proof_repro"
lake build -KwarningAsError=true
lake env lean Audit.lean
sha256sum -c evidence/SHA256SUMS
# Keep the directory for inspection. Logs are collected by the caller.
