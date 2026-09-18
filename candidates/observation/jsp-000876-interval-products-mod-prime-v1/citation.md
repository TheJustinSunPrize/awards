# Candidate observation

## English

This candidate observation is associated with [JSP-000876 — Can several consecutive integer intervals each have product congruent to one modulo the same prime?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000876). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of an explicit instance for the catalog question: the prime `11` admits two **disjoint** consecutive-integer intervals `[3, 4]` and `[5, 7]` whose elementwise products are both congruent to one modulo `11` (`3 * 4 = 12 ≡ 1 (mod 11)` and `5 * 6 * 7 = 210 ≡ 1 (mod 11)`, and the intervals are disjoint since `4 < 5`). The theorem proved is `jsp000876 : ∃ (p a₁ b₁ a₂ b₂ : ℕ), Nat.Prime p ∧ a₁ ≤ b₁ ∧ b₁ < a₂ ∧ a₂ ≤ b₂ ∧ (∏ i ∈ Finset.Icc a₁ b₁, i) % p = 1 ∧ (∏ i ∈ Finset.Icc a₂ b₂, i) % p = 1`.

**Scope boundary:** this observation records only the concrete instance `p = 11` with the two disjoint intervals `[3, 4]` and `[5, 7]`, i.e. the lower bound "several = at least two". It does not address how many such disjoint intervals can exist for a fixed prime (nor whether arbitrarily many or infinitely many exist), does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000876-lean](https://github.com/Yaohua-Leo/jsp-000876-lean) at commit `4508b6cf2c2b0881650de62935a41c06a9c35d8d` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000876.lean` produces zero output, and `#print axioms jsp000876` reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The catalog entry records "No later than 2004 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
