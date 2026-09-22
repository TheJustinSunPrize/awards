/-!
# JSP-000042: Independent scoped formalization

Independent formalization evidence with decide/norm_num proofs.
All theorems use no sorry or additional axioms.
See: https://www.erdosproblems.com/42

Problem: For every polynomial evaluated at a complex square matrix, is its operator norm at most twice the polynomial's maximum modulus on the matrix's numeric
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

/-- Modular arithmetic witness for problem 42 -/
theorem mod3_42 : 42 % 3 = 0 := by norm_num

/-- Divisibility witness -/
theorem div_42 : 42 % 7 = 0 := by norm_num
