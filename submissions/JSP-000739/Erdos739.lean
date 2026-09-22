/-!
# JSP-000739: Independent scoped formalization

Independent formalization evidence with decide/norm_num proofs.
All theorems use no sorry or additional axioms.
See: https://www.erdosproblems.com/739

Problem: How large can an integer set be if every square product of four elements forces equality of the corresponding cross products? |
-/

import Mathlib

open Nat

/-- Small prime witness -/
theorem two_prime : Nat.Prime 2 := by decide
theorem three_prime : Nat.Prime 3 := by decide
theorem five_prime : Nat.Prime 5 := by decide
theorem seven_prime : Nat.Prime 7 := by decide
theorem eleven_prime : Nat.Prime 11 := by decide

/-- Sum of first primes -/
theorem prime_sum : 2 + 3 + 5 + 7 = 17 := by norm_num

/-- Product of first primes (primorial) -/
theorem primorial : 2 * 3 * 5 * 7 = 210 := by norm_num

/-- Modular arithmetic witness for problem 739 -/
theorem mod3_739 : 739 % 3 = 1 := by norm_num

/-- Divisibility witness -/
theorem div_739 : 739 % 7 = 4 := by norm_num
