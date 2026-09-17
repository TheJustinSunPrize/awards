# Candidate observation

## English

This candidate observation is associated with [JSP-000321 — When can two disjoint intervals of consecutive positive integers have equal products?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000321). It publishes `Statement.lean` and `Proof.lean` for one explicit instance of the phenomenon asked about by the catalogued question: the disjoint intervals `[5, 7]` and `[14, 15]` of consecutive positive integers have equal products, `5 * 6 * 7 = 210 = 14 * 15`, with disjointness witnessed by `7 < 14`.

This observation records a complete, machine-checked Lean proof of one explicit instance (5·6·7 = 14·15) of equal products of two disjoint intervals of consecutive positive integers. The classification of all such instances requested by the question is not addressed, the catalogued problem is not resolved, and no award claim is made.

The catalog entry records "Date proposed: No later than 1976 (bibliographic evidence)" and lists no publication details. The posed year of 1976 with basis `earliest-reference` follows the catalog entry; no separate publication of the problem is asserted by this observation. The record schema requires a nonempty citation string, so the `citation` field points to the catalog entry itself as the public record of the problem statement, not to an independent publication.

A local Lean compilation (`lake env lean JSP000321.lean`, exit code 0 with no output) and an axiom audit (`#print axioms equal_product_intervals` reports that the theorem depends on no axioms) were run with Lean v4.35.0-rc2 and the pinned Mathlib v4.35.0-rc2 revision at commit `a4dc1fba91544b777a29ea001b25cd6524c06a0b` of [Yaohua-Leo/jsp-000321-lean](https://github.com/Yaohua-Leo/jsp-000321-lean). These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
