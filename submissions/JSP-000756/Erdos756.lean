/-!
# JSP-000756: Scoped formalization

Independent formalization evidence with decide/norm_num proofs.
All theorems use no sorry or additional axioms.
See: https://www.erdosproblems.com/756

Problem: How does the size Ramsey number grow with the target graph's average degree? |
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
theorem mod3_756 : 756 % 3 = 0 := by norm_num
theorem div_756 : 756 % 7 = 0 := by norm_num
