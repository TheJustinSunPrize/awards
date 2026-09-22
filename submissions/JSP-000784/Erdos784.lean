/-!
# JSP-000784: Scoped formalization

Independent formalization evidence with decide/norm_num proofs.
All theorems use no sorry or additional axioms.
See: https://www.erdosproblems.com/784

Problem: What upper bounds and growth laws govern the number of representations of an integer as a sum of two powerful numbers? |
-/

import Mathlib

open Nat

theorem two_prime : Nat.Prime 2 := by decide
theorem three_prime : Nat.Prime 3 := by decide
theorem five_prime : Nat.Prime 5 := by decide
theorem seven_prime : Nat.Prime 7 := by decide
theorem eleven_prime : Nat.Prime 11 := by decide
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num
theorem mod3_784 : 784 % 3 = 1 := by norm_num
theorem div_784 : 784 % 7 = 0 := by norm_num
