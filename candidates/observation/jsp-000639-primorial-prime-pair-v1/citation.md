# Candidate observation

## English

This candidate observation is associated with [JSP-000639 — For a product of the first several primes, is there always a prime between its largest factor and the product whose sum with the product is also prime?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000639). It publishes `Statement.lean` and `Proof.lean` for complete, machine-checked Lean proofs of explicit prime pairs `(q, q + P)` for the primorials `P` = product of the first `k` primes with `k = 2, 3, 4, 5`: with `Pₖ = 2·3·5·…·pₖ` the recorded witnesses are `q = 5` (P = 6, q + P = 11), `q = 7` (P = 30, q + P = 37), `q = 13` (P = 210, q + P = 223), and `q = 23` (P = 2310, q + P = 2333); in each case `q` is prime, lies strictly between the largest prime factor of `P` and `P` itself, and `q + P` is prime.

**Scope boundary:** this observation records only the explicit witness instances for `k = 2, 3, 4, 5` (the existential side of the question for those `k`). It does not assert the property for all `k`, does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000639-lean](https://github.com/Yaohua-Leo/jsp-000639-lean) at commit `9cfd267a48d7a8640ca5487416567ead7e7cd288` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000639.lean` produces zero output apart from the axiom audit, and `#print axioms` for every theorem reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The catalog entry records "No later than 1983 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
