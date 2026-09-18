# Candidate observation

## English

This candidate observation is associated with [JSP-000880 — How many integers can have a prescribed value of the integer times its divisor sum?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000880). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of the existence component of an observation about the catalogued question: some integers `m` have at least two distinct preimages under `n ↦ n * σ(n)`, where `σ` denotes the sum-of-divisors function. The theorem proved is `jsp000880 : ∃ a b m : ℕ, a ≠ b ∧ a * ArithmeticFunction.sigma 1 a = m ∧ b * ArithmeticFunction.sigma 1 b = m`, with the explicit collision `12 * σ(12) = 14 * σ(14) = 336` (σ(12) = 1+2+3+4+6+12 = 28 and σ(14) = 1+2+7+14 = 24). A brute-force spot check finds 660 such colliding values of `m` below 20000; that count is evidence of how common the phenomenon is and is not part of the formalized statement.

**Scope boundary:** this observation records only the existence of some `m` with at least two distinct preimages under `n ↦ n * σ(n)`. It does not bound how many integers `n` can share a prescribed value of `n * σ(n)`, does not decide whether that multiplicity is unbounded, does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000880-lean](https://github.com/Yaohua-Leo/jsp-000880-lean) at commit `228072c6d48f499d72f1b669b7508ff20a8d0413` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000880.lean` produces zero output, and `#print axioms jsp000880` reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The catalog entry records "No later than 2004 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
