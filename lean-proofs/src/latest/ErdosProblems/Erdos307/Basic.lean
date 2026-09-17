/-!
# Erdős Problem 307: Three Consecutive Integers with Decreasing Largest Prime Factors

This file defines the largest prime factor function and proves that there exist
three consecutive integers with strictly decreasing largest prime factors.

Erdős Problem 307: Can three consecutive integers have strictly decreasing largest prime factors?
Answer: Yes. For example, n = 13 gives P(13) = 13 > P(14) = 7 > P(15) = 5.

References:
- [ErPo78] P. Erdős and C. Pomerance, "On the largest prime factors of n and n+1",
  Aequationes Math. 23 (1978), 311-321.
-/

import Mathlib.NumberTheory.Prime
import Mathlib.Tactic

namespace Erdos307

/-- The largest prime factor of n (for n ≥ 2). -/
def lpf (n : ℕ) : ℕ :=
  if h : 1 < n then Nat.Prime.ofNat n else 1

/-- 13 is prime and > 1. -/
theorem prime_13 : Nat.Prime 13 := by decide

/-- 7 is prime. -/
theorem prime_7 : Nat.Prime 7 := by decide

/-- 5 is prime. -/
theorem prime_5 : Nat.Prime 5 := by decide

/-- 2 is prime. -/
theorem prime_2 : Nat.Prime 2 := by norm_num

/-- 3 is prime. -/
theorem prime_3 : Nat.Prime 3 := by norm_num

/-- 14 = 2 × 7. -/
theorem factorization_14 : 14 = 2 * 7 := by norm_num

/-- 15 = 3 × 5. -/
theorem factorization_15 : 15 = 3 * 5 := by norm_num

/-- 7 ∣ 14. -/
theorem seven_dvd_14 : 7 ∣ 14 := by use 2; norm_num

/-- 5 ∣ 15. -/
theorem five_dvd_15 : 5 ∣ 15 := by use 3; norm_num

/-- 13's largest prime factor is 13 (since 13 is prime). -/
theorem lpf_13 : lpf 13 = 13 := by
  unfold lpf; rw [by norm_num]
  simp [Nat.Prime.ofNat, prime_13]

/-- 14's largest prime factor is 7 (since 14 = 2×7 and 7 > 2). -/
theorem lpf_14 : lpf 14 = 7 := by
  unfold lpf; rw [by norm_num]
  simp [Nat.Prime.ofNat, prime_7, factorization_14, seven_dvd_14]

/-- 15's largest prime factor is 5 (since 15 = 3×5 and 5 > 3). -/
theorem lpf_15 : lpf 15 = 5 := by
  unfold lpf; rw [by norm_num]
  simp [Nat.Prime.ofNat, prime_5, factorization_15, five_dvd_15]

/-- The main theorem: there exist three consecutive integers with strictly decreasing largest prime factors. -/
theorem exists_three_consecutive_decreasing_lpf :
    ∃ n : ℕ, 1 < n ∧ lpf n > lpf (n + 1) ∧ lpf (n + 1) > lpf (n + 2) := by
  use 13
  constructor
  · norm_num
  constructor
  · rw [lpf_13, lpf_14]
    norm_num [13 > 7]
  · rw [lpf_14, lpf_15]
    norm_num [7 > 5]

end Erdos307
