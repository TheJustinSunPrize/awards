# Candidate observation

## English

This candidate observation is associated with [JSP-000566 — How fast can prime chains grow when each prime divides one less than the next?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000566). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of the literal existential instance behind the catalog question: there exists a strictly increasing chain of six primes starting at `2`, namely `2 → 3 → 7 → 29 → 59 → 709`, in which each prime divides one less than the next (`3 − 1 = 1 · 2`, `7 − 1 = 2 · 3`, `29 − 1 = 4 · 7`, `59 − 1 = 2 · 29`, `709 − 1 = 12 · 59`). The main theorem proved is `jsp000566 : ∃ (a b c d e f : ℕ), Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧ Nat.Prime d ∧ Nat.Prime e ∧ Nat.Prime f ∧ a ∣ b − 1 ∧ b ∣ c − 1 ∧ c ∣ d − 1 ∧ d ∣ e − 1 ∧ e ∣ f − 1 ∧ 1 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f`, with a companion list-form theorem for `[2, 3, 7, 29, 59, 709]`. All primality and divisibility facts are discharged by `decide` on the literal numerals inside Lean; no external primality or divisibility facts are assumed.

**Scope boundary:** this observation records only the existence of this single length-6 prime chain starting at 2. It does not address the growth-rate question for arbitrary prime chains, does not address infinitude of such chains, does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000566-lean](https://github.com/Yaohua-Leo/jsp-000566-lean) at commit `646a4b71398f98866cde7e2615cefe63ab013dcf` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000566.lean` produces zero errors and zero warnings, and `#print axioms` for every theorem in the file reports only `[propext, Classical.choice, Quot.sound]` — no `sorryAx` or any other axiom. These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The catalog entry records "No later than 1979 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
