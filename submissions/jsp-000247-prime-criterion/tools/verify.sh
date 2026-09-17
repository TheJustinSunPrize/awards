#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Erdos291Criterion Erdos291Criterion.Audit
lake env lean -E warning Erdos291Criterion/Audit.lean
# Replays the complete imported environment using the bundled Lean kernel.
# This is not an independent verifier implementation.
lake env leanchecker --fresh -v Erdos291Criterion.Audit
