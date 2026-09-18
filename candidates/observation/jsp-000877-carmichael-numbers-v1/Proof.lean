/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000877 — Observation record: the three smallest Carmichael numbers
satisfy the Korselt criterion.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000877):
  "Does the count of Carmichael numbers up to a bound grow with exponent
   approaching one?"
(Carmichael numbers: composite `n` with `b^(n-1) ≡ 1 (mod n)` for every `b`
coprime to `n`.)

Scope of this file
------------------
This file records complete, machine-checked Lean proofs that the three
smallest Carmichael numbers `561 = 3 * 11 * 17`, `1105 = 5 * 13 * 17` and
`1729 = 7 * 13 * 19` are indeed Carmichael numbers (`Nat.IsCarmichael`),
via explicit Korselt certificates: each of them is `> 2`, composite,
squarefree, and every prime factor `p` satisfies `p - 1 ∣ n - 1`.

These are verified witnesses for the *individual instances*.  This file does
NOT prove any general statement about the set of Carmichael numbers (in
particular nothing about the growth of the counting function, which is the
catalogued open problem), does not resolve the catalogued open problem, and
makes no award claim.

Mathematical area: Number theory / Carmichael numbers.
Problem posed: no later than 1956 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

namespace Jsp000877

/-! ## Prime factorizations (decided by kernel computation) -/

/-- `561 = 3 * 11 * 17`. -/
theorem primeFactorsList_561 : (561 : ℕ).primeFactorsList = [3, 11, 17] := by
  simp

/-- `1105 = 5 * 13 * 17`. -/
theorem primeFactorsList_1105 : (1105 : ℕ).primeFactorsList = [5, 13, 17] := by
  simp

/-- `1729 = 7 * 13 * 19`. -/
theorem primeFactorsList_1729 : (1729 : ℕ).primeFactorsList = [7, 13, 19] := by
  simp

/-! ## Explicit Korselt certificates

Korselt's criterion (Korselt 1899): a positive integer `n` is a Carmichael
number if and only if `n` is composite, squarefree, and `p - 1 ∣ n - 1` for
every prime factor `p` of `n`.  The equivalence itself is
`Nat.isCarmichael_iff_korselt` in Mathlib; here we only supply the concrete
certificates. -/

/-- Korselt certificate for `561`: `561 = 3 * 11 * 17` is composite,
squarefree, and `2, 10, 16` all divide `560 = 561 - 1`. -/
theorem korselt_561 :
    2 < 561 ∧ ¬(561 : ℕ).Prime ∧ Squarefree (561 : ℕ) ∧
      ∀ p : ℕ, p.Prime → p ∣ 561 → p - 1 ∣ 561 - 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · -- 561 = 3 * 187 is composite
    exact Nat.not_prime_mul (a := 3) (b := 187) (by norm_num) (by norm_num)
  · -- 561 is squarefree: the primes 3, 11, 17 occur without repetition
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num), primeFactorsList_561]
    decide
  · -- every prime factor of 561 is one of 3, 11, 17
    intro p hp hdvd
    have hmem : p ∈ (561 : ℕ).primeFactorsList :=
      (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hp, hdvd⟩
    rw [primeFactorsList_561] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    exact absurd hmem (by simp)

/-- Korselt certificate for `1105`: `1105 = 5 * 13 * 17` is composite,
squarefree, and `4, 12, 16` all divide `1104 = 1105 - 1`. -/
theorem korselt_1105 :
    2 < 1105 ∧ ¬(1105 : ℕ).Prime ∧ Squarefree (1105 : ℕ) ∧
      ∀ p : ℕ, p.Prime → p ∣ 1105 → p - 1 ∣ 1105 - 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · -- 1105 = 5 * 221 is composite
    exact Nat.not_prime_mul (a := 5) (b := 221) (by norm_num) (by norm_num)
  · -- 1105 is squarefree: the primes 5, 13, 17 occur without repetition
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num), primeFactorsList_1105]
    decide
  · -- every prime factor of 1105 is one of 5, 13, 17
    intro p hp hdvd
    have hmem : p ∈ (1105 : ℕ).primeFactorsList :=
      (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hp, hdvd⟩
    rw [primeFactorsList_1105] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    exact absurd hmem (by simp)

/-- Korselt certificate for `1729`: `1729 = 7 * 13 * 19` is composite,
squarefree, and `6, 12, 18` all divide `1728 = 1729 - 1`. -/
theorem korselt_1729 :
    2 < 1729 ∧ ¬(1729 : ℕ).Prime ∧ Squarefree (1729 : ℕ) ∧
      ∀ p : ℕ, p.Prime → p ∣ 1729 → p - 1 ∣ 1729 - 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · -- 1729 = 7 * 247 is composite
    exact Nat.not_prime_mul (a := 7) (b := 247) (by norm_num) (by norm_num)
  · -- 1729 is squarefree: the primes 7, 13, 19 occur without repetition
    rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num), primeFactorsList_1729]
    decide
  · -- every prime factor of 1729 is one of 7, 13, 19
    intro p hp hdvd
    have hmem : p ∈ (1729 : ℕ).primeFactorsList :=
      (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hp, hdvd⟩
    rw [primeFactorsList_1729] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    rcases List.mem_cons.mp hmem with rfl | hmem
    · decide
    exact absurd hmem (by simp)

/-! ## The three witnesses are Carmichael numbers -/

/-- `561` is a Carmichael number (Korselt certificate + Mathlib's criterion). -/
theorem isCarmichael_561 : Nat.IsCarmichael 561 :=
  Nat.isCarmichael_iff_korselt.mpr korselt_561

/-- `1105` is a Carmichael number (Korselt certificate + Mathlib's criterion). -/
theorem isCarmichael_1105 : Nat.IsCarmichael 1105 :=
  Nat.isCarmichael_iff_korselt.mpr korselt_1105

/-- `1729` is a Carmichael number (Korselt certificate + Mathlib's criterion). -/
theorem isCarmichael_1729 : Nat.IsCarmichael 1729 :=
  Nat.isCarmichael_iff_korselt.mpr korselt_1729

/-- **Main observation for JSP-000877.** The three smallest Carmichael
numbers `561`, `1105` and `1729` are Carmichael numbers, certified through
the Korselt criterion.  This records verified individual witnesses only; no
general statement about Carmichael numbers is claimed. -/
theorem jsp000877_observation :
    Nat.IsCarmichael 561 ∧ Nat.IsCarmichael 1105 ∧ Nat.IsCarmichael 1729 :=
  ⟨isCarmichael_561, isCarmichael_1105, isCarmichael_1729⟩

end Jsp000877

#print axioms Jsp000877.jsp000877_observation
#print axioms Jsp000877.isCarmichael_561
#print axioms Jsp000877.isCarmichael_1105
#print axioms Jsp000877.isCarmichael_1729
#print axioms Jsp000877.korselt_561
#print axioms Jsp000877.korselt_1105
#print axioms Jsp000877.korselt_1729
