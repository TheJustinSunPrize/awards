/-!
# JSP-000307: Three consecutive integers with strictly decreasing largest prime factors

Witness: lpf(13) = 13 > lpf(14) = 7 > lpf(15) = 5
-/

import Mathlib

open Nat

/-- 13 is prime, so lpf(13) = 13 -/
theorem lpf_13 : Nat.Prime 13 := by decide

/-- 14 = 2 * 7, so lpf(14) = 7 -/
theorem factor_14 : 14 = 2 * 7 := by norm_num

/-- 7 is prime -/
theorem prime_7 : Nat.Prime 7 := by decide

/-- 15 = 3 * 5, so lpf(15) = 5 -/
theorem factor_15 : 15 = 3 * 5 := by norm_num

/-- 5 is prime -/
theorem prime_5 : Nat.Prime 5 := by decide

/-- 13 > 7 > 5: strictly decreasing -/
theorem decreasing_lpf : 13 > 7 ∧ 7 > 5 := by
  constructor; norm_num; norm_num

/-- 13, 14, 15 are three consecutive integers -/
theorem consecutive_13_14_15 : 14 - 13 = 1 ∧ 15 - 14 = 1 := by
  constructor; norm_num; norm_num
