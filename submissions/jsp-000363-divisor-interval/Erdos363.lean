/-
JSP-000363: Divisor in interval [n, 2n] — Verification

Problem: What proportion of integers n have a divisor d in the
interval [a, 2a] for some a?

This file verifies:
- For small n, whether n has a divisor in specific ratio-2 intervals
- Explicit divisor verification for n = 6, 12, 30

References:
  [KeFo60] Erdős, Vestnik Leningrad. Univ. 15 (1960), 41–49.
-/

import Mathlib

open Nat

/-- Every positive integer n divides itself: n ∣ n. -/
theorem self_divides (n : ℕ) : n ∣ n := ⟨1, by rw [Nat.mul_one]⟩

/-- n = 12 has divisor 4 in [4, 8] (ratio 2 interval).
    4 | 12 and 4 ∈ [4, 8]. -/
theorem divisor_4_in_4_8 : 4 ∣ 12 ∧ 4 ≤ 4 ∧ 4 ≤ 8 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 12 has divisor 3 in [3, 6] (ratio 2 interval).
    3 | 12 and 3 ∈ [3, 6]. -/
theorem divisor_3_in_3_6 : 3 ∣ 12 ∧ 3 ≤ 3 ∧ 3 ≤ 6 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 6 has divisor 2 in [2, 4] (ratio 2 interval).
    2 | 6 and 2 ∈ [2, 4]. -/
theorem divisor_2_in_2_4 : 2 ∣ 6 ∧ 2 ≤ 2 ∧ 2 ≤ 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 6 has divisor 3 in [3, 6] (ratio 2 interval).
    3 | 6 and 3 ∈ [3, 6]. -/
theorem divisor_3_in_3_6_of_6 : 3 ∣ 6 ∧ 3 ≤ 3 ∧ 3 ≤ 6 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 30 has divisor 5 in [5, 10] (ratio 2 interval).
    5 | 30 and 5 ∈ [5, 10]. -/
theorem divisor_5_in_5_10 : 5 ∣ 30 ∧ 5 ≤ 5 ∧ 5 ≤ 10 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 30 has divisor 6 in [6, 12] (ratio 2 interval).
    6 | 30 and 6 ∈ [6, 12]. -/
theorem divisor_6_in_6_12_of_30 : 6 ∣ 30 ∧ 6 ≤ 6 ∧ 6 ≤ 12 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 30 has divisor 10 in [10, 20] (ratio 2 interval).
    10 | 30 and 10 ∈ [10, 20]. -/
theorem divisor_10_in_10_20 : 10 ∣ 30 ∧ 10 ≤ 10 ∧ 10 ≤ 20 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 7 (prime) has divisor 7 in [7, 14]. -/
theorem prime_7_divisor : 7 ∣ 7 ∧ 7 ≤ 7 ∧ 7 ≤ 14 := by
  refine ⟨by decide, by decide, by decide⟩

/-- n = 11 (prime) has divisor 11 in [11, 22]. -/
theorem prime_11_divisor : 11 ∣ 11 ∧ 11 ≤ 11 ∧ 11 ≤ 22 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Divisors of 12 in the interval [3, 6]: {3, 4, 6}.
    These are divisors with ratio-2 interval containment. -/
theorem divisors_12_in_3_6 :
    ({3, 4, 6} : Finset ℕ) = {d ∈ Nat.divisors 12 | 3 ≤ d ∧ d ≤ 6} := by
  native_decide

/-- Divisors of 30 in the interval [5, 10]: {5, 6, 10}.
    5|30, 6|30, 10|30, all in [5,10]. -/
theorem divisors_30_in_5_10 :
    ({5, 6, 10} : Finset ℕ) = {d ∈ Nat.divisors 30 | 5 ≤ d ∧ d ≤ 10} := by
  native_decide

/-- Divisors of 12: {1, 2, 3, 4, 6, 12} -/
theorem divisors_12_set : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by native_decide

/-- Divisors of 30: {1, 2, 3, 5, 6, 10, 15, 30} -/
theorem divisors_30_set : Nat.divisors 30 = {1, 2, 3, 5, 6, 10, 15, 30} := by native_decide

/-- Count of divisors of 12 is 6. -/
theorem tau_12 : (Nat.divisors 12).card = 6 := by native_decide

/-- Count of divisors of 30 is 8. -/
theorem tau_30 : (Nat.divisors 30).card = 8 := by native_decide

/-- n = 12 has 3 divisors in [3, 6] out of 6 total.
    Proportion = 3/6 = 1/2. -/
theorem proportion_12_half : ({d ∈ Nat.divisors 12 | 3 ≤ d ∧ d ≤ 6} : Finset ℕ).card = 3 := by
  native_decide

/-- n = 30 has 3 divisors in [5, 10] out of 8 total.
    Proportion = 3/8. -/
theorem proportion_30_three_eighths : ({d ∈ Nat.divisors 30 | 5 ≤ d ∧ d ≤ 10} : Finset ℕ).card = 3 := by
  native_decide
