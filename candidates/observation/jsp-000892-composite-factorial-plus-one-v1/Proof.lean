/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000892 — Observation record: explicit composite divisors of factorial
plus one.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000892):
  "How many composite integers divide some factorial plus one, and how are
   they distributed?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the literal
existence component of the catalog question: there exist a composite
integer `n` and a factorial-plus-one `k! + 1` such that `n ∣ k! + 1`.
The witnesses are of the trivial self-divisibility kind: `k! + 1` itself
is composite, hence divides itself:

  * `4! + 1 = 25 = 5^2`   is composite and `25   ∣ 4! + 1`;
  * `5! + 1 = 121 = 11^2` is composite and `121  ∣ 5! + 1`;
  * `7! + 1 = 5041 = 71^2` is composite and `5041 ∣ 7! + 1`.

It does NOT address the quantitative part of the catalog question (how
many such composite integers there are, or how they are distributed),
does not resolve the catalogued open problem, and makes no award claim.

Mathematical area: Number theory.
Problem posed: no later than 2002 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).

Proof notes
-----------
* The Mathlib version pinned for this record (v4.35.0-rc2) does not
  provide a `Nat.Composite` definition, so the classical notion is spelled
  out here as `Composite n := 1 < n ∧ ¬ Nat.Prime n` (composite = greater
  than one and not prime).
* In the main theorem the factorial is written `Nat.factorial k` rather
  than with the scoped postfix notation `k!`; both denote the same term
  (`k!` *is* notation for `Nat.factorial k`).  The explicit constant form
  is used because the scoped notation's delayed elaboration interferes
  with the elaboration of the existential witness term on this toolchain.
* Compositeness of the witnesses is proved from the explicit square
  factorizations `25 = 5 * 5`, `121 = 11 * 11`, `5041 = 71 * 71` via
  `Nat.not_prime_mul`; the divisibility `n ∣ k! + 1` is the trivial
  self-divisibility, obtained by evaluating `k! + 1` with `norm_num`
  (a `decide`-only treatment of the primality part is avoided because
  kernel reduction of the primality decider does not scale to `5041`).
-/

import Mathlib

/- In the Mathlib version pinned for this record, the factorial
notation `n!` is scoped to the `Nat` namespace. -/
open Nat

/-- A natural number is *composite* if it is greater than `1` and not
prime.  (The Mathlib version pinned for this record does not ship a
`Nat.Composite` definition, so the classical notion is spelled out here.
The definition is reducible so that instance search can see through it.) -/
@[reducible]
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

/-- `25 = 5^2` is composite. -/
theorem jsp000892_composite_25 : Composite 25 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (25:ℕ) = 5 * 5 from by norm_num]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `4! + 1 = 25`, so `25 ∣ 4! + 1` (trivial self-divisibility). -/
theorem jsp000892_dvd_25 : (25:ℕ) ∣ 4! + 1 := by
  rw [show (4:ℕ)! + 1 = 25 from by norm_num]

/-- **Explicit witness for JSP-000892 (literal existence component).**

There exist a composite integer `n` and a natural number `k` with
`n ∣ k! + 1`: take `n = 25 = 5^2` and `k = 4`, since `4! + 1 = 25 = 5^2`
is composite and divides itself.  (`Nat.factorial k` is spelled out
because the scoped `k!` notation interferes with witness-term elaboration
on this toolchain; the statement is the intended `n ∣ k! + 1`.) -/
theorem jsp000892 :
    ∃ (n k : ℕ), Composite n ∧ n ∣ Nat.factorial k + 1 :=
  ⟨25, 4, jsp000892_composite_25, jsp000892_dvd_25⟩

/-- `121 = 11^2` is composite. -/
theorem jsp000892_composite_121 : Composite 121 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (121:ℕ) = 11 * 11 from by norm_num]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `5! + 1 = 121`, so `121 ∣ 5! + 1` (trivial self-divisibility). -/
theorem jsp000892_dvd_121 : (121:ℕ) ∣ 5! + 1 := by
  rw [show (5:ℕ)! + 1 = 121 from by norm_num]

/-- Second witness: `5! + 1 = 121 = 11^2` is composite and `121 ∣ 5! + 1`. -/
theorem jsp000892_witness_121 : Composite 121 ∧ 121 ∣ 5! + 1 :=
  ⟨jsp000892_composite_121, jsp000892_dvd_121⟩

/-- `5041 = 71^2` is composite. -/
theorem jsp000892_composite_5041 : Composite 5041 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (5041:ℕ) = 71 * 71 from by norm_num]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-- `7! + 1 = 5041`, so `5041 ∣ 7! + 1` (trivial self-divisibility). -/
theorem jsp000892_dvd_5041 : (5041:ℕ) ∣ 7! + 1 := by
  rw [show (7:ℕ)! + 1 = 5041 from by norm_num]

/-- Third witness: `7! + 1 = 5041 = 71^2` is composite and `5041 ∣ 7! + 1`. -/
theorem jsp000892_witness_5041 : Composite 5041 ∧ 5041 ∣ 7! + 1 :=
  ⟨jsp000892_composite_5041, jsp000892_dvd_5041⟩

#print axioms jsp000892
#print axioms jsp000892_composite_25
#print axioms jsp000892_dvd_25
#print axioms jsp000892_composite_121
#print axioms jsp000892_dvd_121
#print axioms jsp000892_witness_121
#print axioms jsp000892_composite_5041
#print axioms jsp000892_dvd_5041
#print axioms jsp000892_witness_5041
