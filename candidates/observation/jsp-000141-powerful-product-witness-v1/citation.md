# Candidate observation

## English

This candidate observation is associated with [JSP-000141 — Can a product of consecutive positive integers have every prime factor occurring with exponent at least two?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000141). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of an explicit witness for the literal yes/no reading of the catalog question: the product `8 * 9 = 72 = 2^3 * 3^2` of the consecutive positive integers `8` and `9` is a powerful number, i.e. every prime factor `p ∣ 72` satisfies `p^2 ∣ 72`. The theorem proved is `powerful_product_witness : (8:ℕ) * 9 = 72 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ 72 → p ^ 2 ∣ 72`.

**Scope boundary:** this observation records only the explicit witness `8 * 9 = 72` for the literal yes/no reading of the catalog question. It does not address stronger readings (e.g. products of three or more consecutive integers, uniqueness or classification of such witnesses), does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000141-lean](https://github.com/Yaohua-Leo/jsp-000141-lean) at commit `63720364b20038d8e3049d750bf99810622a1a28` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000141.lean` produces zero output, and `#print axioms powerful_product_witness` reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The catalog entry records "No later than 1980 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
