# Candidate observation

## English

This candidate observation is associated with [JSP-000332 — How high a power of a prescribed prime can divide a sum of distinct factorials?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000332). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of two explicit existence witnesses for the observation "there is a sum of at least two distinct factorials that is exactly a prime power": `2! + 3! + 4! = 2 + 6 + 24 = 32 = 2^5` (the sum over the index set `{2, 3, 4}` equals the fifth power of the prime `2` exactly) and `1! + 2! + 4! = 1 + 2 + 24 = 27 = 3^3` (the sum over the index set `{1, 2, 4}` equals the third power of the prime `3` exactly). In both witnesses the displayed equation pins the exponent exactly — the sum equals the prime power, no more and no less. The theorems proved are `jsp000332_instance_two`, `jsp000332_instance_three`, and their conjunction `jsp000332`.

**Scope boundary:** this observation records only the two explicit existence witnesses above. It does not answer the catalog question for a general prescribed prime — no statement is made about the highest power of a given prime dividing a given sum of distinct factorials, nor about classification of all such witnesses — does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000332-lean](https://github.com/Yaohua-Leo/jsp-000332-lean) at commit `2ea822acf72f18b0c9dd97589c330b496e87c886` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000332.lean` produces zero output, and `#print axioms` reports for all three theorems exactly `[propext, Quot.sound]` (within the allowed set `propext, Classical.choice, Quot.sound`; a `decide`-only proof may report a subset). These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The catalog entry records "No later than 1980 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
