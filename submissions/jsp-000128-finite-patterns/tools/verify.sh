#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Erdos120FinitePatterns Erdos120FinitePatterns.Audit
lake env lean -E warning Erdos120FinitePatterns/Audit.lean
# Full imported-environment replay through the bundled Lean kernel.
# This is not an independent verifier implementation.
lake env leanchecker --fresh -v Erdos120FinitePatterns.Audit
