# JSP-000478 / Erdős 589: the classical greedy bound

Lean 4.34.0 formalization of the classical greedy general-position bound.
For every finite set `A` of real planar points with no four collinear,
there is a subset `B` with no three collinear satisfying
`|A| ≤ |B| + choose(|B|, 2)`. Consequently `2|A| ≤ |B|(|B|+1)` and
`|A| ≤ |B|²`, the finite cardinality form of the classical square-root
guarantee.

This is the known greedy argument described on the
[Erdős Problem 589 page](https://www.erdosproblems.com/589).
The stronger known bounds and optimal asymptotic problem are outside
this submission. Only consideration for a formalization contribution is
requested; mathematical discovery, priority, eligibility and an award
are not claimed.

## Statement and proof

[GeneralPositionBound.lean](GeneralPositionBound.lean) uses actual points
of `ℝ × ℝ` and Mathlib's standard `Collinear` predicate. A proved
equivalence `boundedLines_iff` connects the finite-subset definitions to
the usual “no three/four distinct collinear points” wording.

The main theorems are `GeneralPositionBound.greedy_bound`,
`greedy_quadratic_bound` and `greedy_square_bound`. They include empty
and small sets. See [STATEMENT.md](STATEMENT.md) for exact definitions,
scope and attribution.

Choose a maximum-cardinality general-position subset `B`. Every point
outside `B` lies on a line through a pair of its points, and each such
pair blocks at most one outside point because `A` has no four collinear.
Counting those pairs gives the claimed inequality. This entire argument
is proved; no unproved greedy-bound hypothesis is introduced.

## Reproduce

Use Python 3.10+, Git and the official Lean 4.34.0 toolchain, with `lean`
and `lake` on PATH. All package revisions are pinned in the manifest.
From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get --cache-from=master Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional Mathlib.Basic.Real.Basic Mathlib.Data.Finset.Powerset Mathlib.Data.Nat.Choose.Cast Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Push
python3 -O verify.py
python3 -m unittest discover -s tests -v
```

The verifier builds the proof, compiles [Audit.lean](Audit.lean) with
warnings as errors, audits the named theorems' axiom dependencies, runs
negative controls and replays the imported environment in a fresh Lean
kernel. Its outputs are [verification.json](evidence/verification.json)
and [axioms.txt](evidence/axioms.txt). The regression tests check that
validation gates remain active under Python optimization, including
failure paths; they are separate from the real Lean verification.

The audited theorems depend only on the standard `propext`,
`Classical.choice` and `Quot.sound` axioms. The proof uses no placeholders,
custom axioms, native-evaluation shortcut or external-solver assumptions.
`python3 verify.py --skip-replay` is available for a shorter rerun and
explicitly records that replay was omitted.

`leanchecker --fresh` uses the bundled Lean kernel, not a separately
implemented checker. Upstream cache artifacts were used; this is not a
complete source rebuild of every imported library. Local checks and
repository CI do not constitute organizer verification or an award.

Code is MIT licensed. Dependencies retain their own licenses; repository
documentation and record data follow the host repository's
`LICENSE-CONTENT` when included there.
