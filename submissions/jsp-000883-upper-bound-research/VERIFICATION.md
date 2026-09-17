# Checks completed and proof status

The manuscript is a mathematical proof claim offered for review. It has not
received independent peer acceptance and is not a completed Lean proof.

## Actual reproduced results

- All 18 Python tests passed.
- All 1,454 eligible parameter pairs for `9 <= k <= 300` passed exact integer
  checks of all `k` divisibilities of the actual binomial coefficient.
- The cases cover 285 values of `k`: 1,055 left intervals and 399 right intervals.
- Values `10,11,14,15,16,17,26` have no eligible prime under this construction's
  hypotheses and were skipped, not counted as successful cases.
- `Targets.lean` was checked using Lean 4.33.0 and Mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`, with exit code 0. The check reused an
  existing pinned library environment; no clean build of this target project's
  complete Lake workspace is claimed.
- Actual `#print` inspection confirms all four core claims are **definitions
  of propositions**, not theorems proving those propositions.

The compact logs are [Python tests](evidence/python-tests.log),
[finite checks](evidence/finite-checks.log), and
[Lean declaration inspection](evidence/definitions-audit.log).
The source bundle in the release also contains every reproduced finite case.

## What has not been established

No universal Lean proof of `FiniteConstructionClaim`,
`EventualPrimeIntervalClaim`, `EventualUpperClaim`, or `BetterUpperClaim` is
provided. No final-theorem axiom audit or kernel replay can be claimed for
those unproved propositions. The prime-number-theorem input remains an informal
standard theorem in the written argument. Passing tests or compiling a
proposition definition does not prove it.

The valuation proof was examined step by step without finding an obvious
gap. That review and the computation were AI-assisted and are not independent
human refereeing. A formal target's continued placeholder does not establish
that no proof exists elsewhere.

This research publication does not request the official catalog to mark the
problem solved or Lean-verified. Passing the award repository's structural
checks only establishes document/schema consistency.
