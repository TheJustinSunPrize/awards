#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake --wfail build Erdos141FirstCases Erdos141FirstCases.Audit
lake env lean -E warning Erdos141FirstCases/Audit.lean
# Replays the full imported environment with the bundled Lean kernel.
# This is not an independent verifier implementation.
lake env leanchecker --fresh -v Erdos141FirstCases.Audit
