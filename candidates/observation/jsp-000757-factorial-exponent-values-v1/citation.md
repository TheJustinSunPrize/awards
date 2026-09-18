# Candidate observation

## English

This candidate observation is associated with [JSP-000757 — How many distinct exponent values occur in the prime factorization of a factorial?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000757). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of the exact `n = 10` instance of the catalog question: the prime factorization of `10! = 3628800` is `2^8 · 3^4 · 5^2 · 7^1`, so the multiset of prime-factor exponents of `10!` is `{8, 4, 2, 1}` — exactly four distinct exponent values. The theorem proved is `jsp000757 : ∃ (V : Finset ℕ), V.card = 4 ∧ V = {8, 4, 2, 1} ∧ ∀ p : ℕ, Nat.Prime p → ((p ∣ Nat.factorial 10 → expo p ∈ V ∧ p ^ expo p ∣ Nat.factorial 10 ∧ ¬ p ^ (expo p + 1) ∣ Nat.factorial 10) ∧ (¬ p ∣ Nat.factorial 10 → expo p = 0))`, i.e. for every prime `p`, `expo p` is exactly the exponent of `p` in `10!` when `p ∣ 10!`, and `0` otherwise.

**Scope boundary:** this observation records only the exact instance `n = 10` of the catalog question (the set of exponent values occurring in the prime factorization of `10!` is `{8, 4, 2, 1}`, of cardinality `4`). It does not address the question for general factorials `n!` (e.g. the growth or distribution of the number of distinct exponent values as `n` varies), does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000757-lean](https://github.com/Yaohua-Leo/jsp-000757-lean) at commit `c4f6fc48c8fc1bc0b86ec59d095d509e29c72414` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000757.lean` produces zero output, and `#print axioms jsp000757` reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The catalog entry records "No later than 1982 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
