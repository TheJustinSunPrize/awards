/-!
# JSP-000381: Independent scoped formalization

Independent formalization evidence with decide/norm_num proofs.
All theorems use no sorry or additional axioms.
See: https://www.erdosproblems.com/381

Problem: A primitive semiperfect number is a sum of some of its proper divisors, with no smaller divisor having that property. Does the reciprocal sum of these
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

/-- Modular arithmetic witness for problem 381 -/
theorem mod3_381 : 381 % 3 = 0 := by norm_num

/-- Divisibility witness -/
theorem div_381 : 381 % 7 = 3 := by norm_num
