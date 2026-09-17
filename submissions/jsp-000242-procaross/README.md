# JSP-000242: certified finite optima for distinct unit fractions

This package proves the maximum possible smallest denominator in a representation
of one by exactly `k` distinct positive unit fractions, for every `k` from 3 through
12. It also proves a complete decision procedure for the fixed-cardinality
representation problem with any rational target and any positive lower bound on
the denominators.

## Mathematical statement

Let `B(k)` be the greatest achievable value of `min A`, where `A` is a finite set
of `k` distinct positive integers and `sum (1/a for a in A) = 1`.

| `k` | `B(k)` | One attaining denominator set |
| --- | --- | --- |
| 3 | 2 | 2, 3, 6 |
| 4 | 2 | 2, 3, 7, 42 |
| 5 | 3 | 3, 4, 5, 6, 20 |
| 6 | 3 | 3, 4, 5, 6, 30, 60 |
| 7 | 3 | 3, 4, 5, 7, 30, 42, 60 |
| 8 | 4 | 4, 5, 6, 7, 8, 15, 40, 42 |
| 9 | 4 | 4, 5, 6, 7, 8, 20, 40, 42, 60 |
| 10 | 5 | 5, 6, 7, 8, 9, 10, 12, 40, 42, 45 |
| 11 | 6 | 6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28 |
| 12 | 6 | 6, 7, 8, 9, 10, 11, 12, 18, 22, 33, 40, 42 |

Each upper bound quantifies over all finite sets of positive integer denominators.
There is no imposed maximum denominator. The small witnesses in the table do not
restrict the range covered by the upper-bound proofs.

The formal set of achievable minima is `UnitFractionBounds.AttainableMinimum` in
[UnitFractionBounds.lean](UnitFractionBounds.lean). It requires the exact set
cardinality, positivity of every denominator, a rational reciprocal sum of one,
membership of the proposed minimum, and its being a lower bound for the set.
The ten `exact_three` through `exact_twelve` theorems have the form
`IsGreatest {m | AttainableMinimum k m} B`, so each combines attainment and
optimality. Distinctness is enforced by `Finset`; division is in `ℚ`.

## Why the search covers unbounded denominators

For a positive remaining rational sum `r` and `k` remaining denominators, the next
denominator `d` satisfies `d <= floor(k/r)`: all `k` terms are at most `1/d`.
Strictly increasing denominators starting at `m` also satisfy the upper bound
`1/m + 1/(m+1) + ... + 1/(m+k-1)` on their reciprocal sum. These two elementary
facts give a finite recursive search, decreasing the remaining number of terms.

`possible_of_rep` proves that the search never discards an actual increasing
representation. `rep_of_possible` constructs a representation from every positive
answer. `possible_iff_finset` transfers both directions to ordinary finite sets:

```lean
possible k m r = true ↔
  ∃ A : Finset ℕ, A.card = k ∧
    (∀ a ∈ A, m ≤ a) ∧ (∑ a ∈ A, (1 : ℚ) / a) = r
```

The hypothesis is `0 < m`. The statement includes all natural cardinalities and
all rational targets; it does not assume a successful representation exists.
False certificates at `m = B(k)+1` establish the upper bounds. Explicit sets
establish attainment. The certificates use `decide +kernel`, and the positive
equalities use `norm_num`. All proof terms are checked by Lean's kernel.

For example, the simple consecutive-denominator bound permits `B(7) <= 4`,
because `1/4 + ... + 1/10 > 1`. The recursive certificate proves the stronger
exact result `B(7) = 3`.

## Scope, attribution, and review request

The source problem is
[JSP-000242 at the reviewed catalog revision](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000242).
The catalog cites E. S. Croot III, *On unit fractions with denominators in short
intervals*, Acta Arithmetica 99 (2001), 99–114,
[DOI](https://doi.org/10.4064/aa99-2-1),
[author's preprint](https://arxiv.org/abs/math/9904181). The original problem family
is due to Erdős and Graham. Credit for that mathematics and Croot's asymptotic
work remains with its authors.

The proposed contribution is this Lean decision procedure, its finite-set
equivalence theorem, and the ten exact finite certificates. The package does not
formalize the catalog's full asymptotic result. The elementary search method and
finite values are not claimed as new mathematics, and no global first-formalization
priority is asserted. [Duplicate screening](DUPLICATE-SEARCH.md) records the
reviewed neighboring submissions and the limits of the searches.

Public submitter: `procaross`. The Lean implementation and documentation were
prepared with OpenAI ChatGPT/Codex assistance. Proposed formalizer recipient ID:
`RECIPIENT-JSP-000242-PROCAROSS-A`, identity/recipient confirmation pending.
This is a scoped formalization submission for review of correspondence,
attribution, overlap, usefulness, and eligibility. It supplies no organizer
decision, award acceptance, or payment entitlement.

## Reproduction

Requirements: Python 3.10 or later, Git, and Elan with the toolchain specified in
[lean-toolchain](lean-toolchain). The Mathlib commit and every transitive Git
dependency are locked in [lake-manifest.json](lake-manifest.json).

From this directory:

```sh
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LEAN_NUM_THREADS=1
lake exe cache get Mathlib.Data.Finset.Sort Mathlib.Data.Rat.Floor \
  Mathlib.Algebra.BigOperators.Group.List.Basic \
  Mathlib.Algebra.BigOperators.Group.Finset.Basic \
  Mathlib.Order.Interval.Finset.Nat Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith
lake build
python3 verify.py
```

`verify.py` checks the pinned source and Mathlib configuration hashes; compiles with
implicit variables disabled and warnings treated as errors; checks sixteen axiom
reports against `propext`, `Classical.choice`, and `Quot.sound`; replays the module
with the bundled `leanchecker`; checks two correct certificates in an importing
file; and requires rejection of an intentionally false certificate for the
classical set `{2,3,6}` in the same environment. Fresh reports are written under
`verification/latest/`.

The [recorded local run](verification/local/verification.json) passed compilation,
all sixteen axiom audits, and module replay on Lean 4.34.0. Its intentionally
false control exited with code 1 as required. The accompanying short logs and
source hashes identify exactly what was checked. The local run reused pinned
archive-based Mathlib dependencies; the standalone Lake package was also built
successfully with those exact dependency paths.

The verification runner can be executed in another Lean environment using the
commands above. This submission does not add a GitHub Actions proof job.
The ordinary award-record CI checks repository records and links; it does not
execute these mathematical proofs.

The bundled `leanchecker` uses Lean's own kernel. It is not an independently
implemented verifier. Imported Lean/Mathlib declarations are trusted rather than
replayed from scratch; there has been no independent human verification or
organizer assessment of this package.

The source is released under the Apache 2.0 license. Imported libraries retain
their original licenses and attribution.
