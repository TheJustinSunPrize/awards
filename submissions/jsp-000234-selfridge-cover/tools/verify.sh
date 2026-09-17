#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Erdos273Selfridge Erdos273Selfridge.Audit
lake env lean -E warning Erdos273Selfridge/Audit.lean
# Full imported-environment replay, using the bundled Lean kernel.
# This is not an independent verifier implementation.
lake env leanchecker --fresh -v Erdos273Selfridge.Audit
