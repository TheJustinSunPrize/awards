# JSP-000883 / Erdős 1063: Monier's factorial upper bound

## English

This package gives a new Lean proof of the known bound `n k ≤ k!` for every
`k ≥ 3`, where `n k` is the least `m ≥ 2k` for which exactly one of
`m, m-1, ..., m-k+1` fails to divide `m.choose k`.
It also proves the full witness at `m = k!` and that the exact threshold
satisfies its defining property for every `k ≥ 2`.

**This is a formalization of a known partial result, not a solution of the
open growth-rate problem.** Monier proved the mathematics in 1985. Cambie's
stronger least-common-multiple bound is known and is not formalized here.
No new or improved mathematical bound is claimed.

The definition `Erdos1063.n` is reproduced from the pinned Formal Conjectures
source under Apache-2.0. Its unproved theorems are not imported.

## Reproduction

Install Elan, then run from this directory:

```sh
lake exe cache get Mathlib.Algebra.BigOperators.ModEq Mathlib.Data.Nat.Factorial.BigOperators Mathlib.Data.Nat.Choose.Basic Mathlib.Order.ConditionallyCompleteLattice.Basic Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
lake env lean -DwarningAsError=true Prize1063.lean
python3 scripts/verify.py
lake env leanchecker --verbose --fresh Prize1063
```

Lean and every dependency revision are pinned. See [statement correspondence](STATEMENT.md),
[prior-art screening and attribution](PRIOR_ART.md), and
[verification evidence](evidence/verification.json).
The local checks use cached pinned dependencies. A complete source rebuild of
mathlib, independent checker implementation, and independent human review are
not claimed. Fresh replay uses the bundled Lean kernel.

## Requested review

Please evaluate this 2026 formalization of a known partial result under the
[published prize rules](https://www.hejustinsun.com/prize/rules), including
Sections 2.5, 4.2, and 5. Consider the applicant for the Lean formal verifier
role (30% of any eligible allocation), not the solver role.
Whether this specific scope qualifies, priority, award tier, and amount remain
for designated verification and committee adjudication. None is asserted.

The proposed recipient is `RECIPIENT-jsp-000883-A`, pending confirmation.
This is a self-submission prepared by the applicant with ChatGPT assistance;
the applicant has a direct interest in its award outcome.
The package proposes a Lean-containing intake PR; it does not alter catalogue,
candidate, recipient, or award records. It claims no second payment for its
helper theorem or existence corollary.
