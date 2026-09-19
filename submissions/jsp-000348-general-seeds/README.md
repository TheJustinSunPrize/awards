# JSP-000348: arbitrary positive seeds

This package formalizes the qualitative arbitrary-seed extension described in
[Quanyu Tang, arXiv:2603.09939v2, Section 6.1](https://arxiv.org/html/2603.09939v2#S6.SS1).
For every finite list of positive integers of length at least two, its greedy
consecutive-sum extension exists uniquely, its excess above the index tends to
infinity, and it omits infinitely many positive integers. The seed may be
unsorted and may contain repeated values.

This is a scoped formalization contribution for
[JSP-000348 / Erdős 423](https://www.erdosproblems.com/423), not a solution of
the open asymptotic question `a_n = n + o(n)`. The arbitrary-seed mathematical
conclusion is credited to Tang. No global formalization-priority or prize
eligibility claim is made.

## Contribution and prior work

[Awards PR #415](https://github.com/TheJustinSunPrize/awards/pull/415) and
[issue #416](https://github.com/TheJustinSunPrize/awards/issues/416) already cover
the classical seed `(1,2)`, including a quantitative lower bound. This package
does not resubmit that as new work. It supplies arbitrary positive seeds,
existence and uniqueness, and a general theorem requiring only eventual
increase and block generation. The proof uses an elementary square-gap
argument. Adapted code patterns and licenses are recorded in
[NOTICE](NOTICE) and [PRIOR_ART.md](PRIOR_ART.md).

## Files

- [GeneralSeeds.lean](GeneralSeeds.lean): definitions and 17 named theorems.
- [STATEMENT.md](STATEMENT.md): precise quantifiers and relation to the original problem.
- [PROOF.md](PROOF.md): mathematical argument and correspondence to the code.
- [Audit.lean](Audit.lean): axiom closure of every named theorem.
- [verification/verification.json](verification/verification.json): commands, timings and hashes.

## Reproduction

Install the compiler specified in `lean-toolchain` (Lean 4.34.0). The manifest
pins Mathlib and all nine dependency revisions. From this directory:

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Data.Nat.Prime.Basic Mathlib.Order.Lattice.Nat Mathlib.Algebra.Ring.Parity Mathlib.Order.ConditionallyCompleteLattice.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
python3 tools/verify.py
```

The verification script checks dependency revisions and tracked-source cleanliness,
builds the proof, audits its axioms, runs finite definition checks, and invokes
`lake env leanchecker --fresh --verbose GeneralSeeds`. The last step reloads and
rechecks the imported declarations and this module in the official Lean kernel.
It is not an independent kernel implementation. Compiled dependency caches are
used; a complete dependency source rebuild is not claimed.

All development, writing and verification were AI-assisted using OpenAI GPT/Codex,
under the submitter's direction. Public submitter ID: `green3sf`. This is a
self-submission; no organizer relationship is asserted. Review and any award
decision remain with the organizers. See [PRIOR_ART.md](PRIOR_ART.md) for the
catalog's current eligibility limitation.
