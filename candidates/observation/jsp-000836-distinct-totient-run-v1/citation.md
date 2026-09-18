# Candidate observation

## English

This candidate observation is associated with [JSP-000836 — How long a consecutive-integer interval can have pairwise distinct totient values?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000836). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of a lower-bound witness for the catalog question: the seven consecutive integers `17, 18, 19, 20, 21, 22, 23` have pairwise distinct Euler totient values, namely `φ(17) = 16, φ(18) = 6, φ(19) = 18, φ(20) = 8, φ(21) = 12, φ(22) = 10, φ(23) = 22`. The theorems proved are `jsp000836 : ∃ (a k : ℕ), 7 ≤ k ∧ ∀ i < k, ∀ j < k, i ≠ j → Nat.totient (a + i) ≠ Nat.totient (a + j)` (with witness `a = 17`, `k = 7`) and the equivalent finite-range formulation `jsp000836'` over `Finset.Icc 17 23`; both are discharged by `decide` over the finite 49-pair comparison.

**Scope boundary:** this observation records only the existence of a consecutive-integer interval of length 7 with pairwise distinct totient values, i.e. a lower bound on the maximal length sought by the catalog question. It does not determine that maximal length, does not address whether the length is unbounded, does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000836-lean](https://github.com/Yaohua-Leo/jsp-000836-lean) at commit `86afa4218ccd787bdef4001f1a8e79dc3a2953ab` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000836.lean` produces no errors or warnings, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for both theorems. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The catalog entry records "No later than 1985 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

This observation is complementary to the repeated-totient collision phenomenon recorded for JSP-000835 in awards PR #899 (`φ(15) = φ(16) = 8`): there a short interval is forced to contain a repeated totient value, whereas here a short interval of length 7 is shown to have all totient values pairwise distinct.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
