#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Erdos261Finite.FiniteBound
lake env lean Erdos261Finite/Audit.lean
# This replays the complete imported environment through the bundled Lean kernel.
# It is not an independent implementation of Lean's verifier.
lake env leanchecker --fresh -v Erdos261Finite.FiniteBound
