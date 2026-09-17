#!/bin/sh
set -eu
cd "$(dirname "$0")"
lean --version
lake exe cache get Mathlib.NumberTheory.Chebyshev Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
lake build
lake env lean Submission.lean
lake env leanchecker -v OneCarry FiniteConstruction Simultaneous SizeBounds Parameters AsymptoticBound Submission
