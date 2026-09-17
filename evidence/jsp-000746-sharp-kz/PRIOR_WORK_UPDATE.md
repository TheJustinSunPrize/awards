# Prior-work clarification for the JSP-000746 supplement

This note supplements, rather than replaces, the earlier README and proof history. No Lean source, statement, or verification result is changed.

## Additional related work identified before official submission

- [Official PR #165](https://github.com/TheJustinSunPrize/awards/pull/165) submits another formalization of the positive independent-Schur-triple theorem.
- Its [pinned prior-source audit](https://github.com/xpzwzwz/jsp-000746-lean/blob/927bc61467102b7bcc34e07419dc585e3c370ee3/evidence/SOURCES.md) identifies an earlier 42-edge Lean lower-bound witness on positive labels 1,...,17 in `rjwalters/lean-genius`, commit `dc62f771ed5010abfdb04247dff6143e0e69d3e7`, file `proofs/Proofs/Erdos895CounterexampleFin18.lean`. This note records that audit; it does not claim a fresh reproduction of that external repository.

Consequently, the README's comparison with the selected `plby/lean-proofs` upper-bound module must not be interpreted as asserting that no earlier lower-bound formalization existed anywhere. In particular, this submission does not claim the first Lean 17-vertex witness, the first formalization of sharpness, the first proof of the original problem, or priority over PR #165.

The proposed contribution is limited to the actual code and evidence supplied: the separately presented 43-edge witness, the restriction argument, the exact-threshold equivalence using the attributed existing upper bound, and the recorded finite cross-checks. Whether any of this is sufficiently distinct and substantial for recognition, given earlier work, remains for the organizers to decide. No mathematical novelty or award entitlement is asserted.

Please review this package alongside issue #19, PR #165, and the earlier lower-bound source, preserving their attribution. The submitting account's AI assistance and self-interest remain as disclosed in the README.

## Artifact retention and submission status

The successful proof artifact has ID `10476738843`, size 84,832 bytes, and ZIP SHA-256 `e8931676c8664efe515edab27190b5f92f706af6bbafa1b9116650914194099f`. Its advertised expiry is December 16, 2026 UTC. This is finite-retention storage, not a permanent independent archive.

At the preparation of this note, creating the upstream PR through the connected integration returned HTTP 403 (`Resource not accessible by integration`). That failed request did not create an official submission. This branch and note are preparation material in the submitting account's fork, not an organizer acceptance or award decision.
