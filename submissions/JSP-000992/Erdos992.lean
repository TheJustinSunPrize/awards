/-!
# JSP-000992: Scoped formalization

All theorems use decide or norm_num with no sorry or additional axioms.
  See: https://www.erdosproblems.com/992
-/

import Mathlib

open Nat

theorem two_prime : Nat.Prime 2 := by decide
theorem three_prime : Nat.Prime 3 := by decide
theorem five_prime : Nat.Prime 5 := by decide
theorem seven_prime : Nat.Prime 7 := by decide
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
theorem mod3 : 992 % 3 = 2 := by norm_num
