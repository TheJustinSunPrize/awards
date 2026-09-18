# Candidate observation

## English

This candidate observation is associated with [JSP-000892 — How many composite integers divide some factorial plus one, and how are they distributed?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000892). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of the literal existence component of the catalog question: there exist a composite integer `n` and a natural number `k` such that `n ∣ k! + 1`. The witnesses are of the trivial self-divisibility kind, namely the factorial-plus-one values that are themselves composite: `4! + 1 = 25 = 5^2`, `5! + 1 = 121 = 11^2`, and `7! + 1 = 5041 = 71^2`. The main theorem proved is `jsp000892 : ∃ (n k : ℕ), Composite n ∧ n ∣ Nat.factorial k + 1` (with `Composite n := 1 < n ∧ ¬ Nat.Prime n` spelled out, since Mathlib v4.35.0-rc2 does not ship a `Nat.Composite` definition), together with explicit instance theorems for the three witnesses above.

**Scope boundary:** this observation records only the literal existence component of the catalog question, witnessed by composite `k! + 1` values that divide themselves. It does not address the quantitative part of the question (how many composite integers divide some factorial plus one, or how they are distributed), does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000892-lean](https://github.com/Yaohua-Leo/jsp-000892-lean) at commit `76cf765a1a0cd13552de6134caf03447a5500a39` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000892.lean` produces zero errors and zero warnings, and `#print axioms` for every theorem in the file reports only `[propext, Classical.choice, Quot.sound]` or `[propext]` — no `sorryAx` or any other axiom. These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The catalog entry records "No later than 2002 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
