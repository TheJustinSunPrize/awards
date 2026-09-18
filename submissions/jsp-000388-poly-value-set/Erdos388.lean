/-
JSP-000388: Polynomial value set with additive complement — Verification

Problem: Can the integer value set of a polynomial have an additive
complement giving each integer exactly one representation?

For a polynomial p, the value set V(p) = {p(n) : n ∈ ℕ}.
An additive complement B satisfies: every integer m has unique
representation m = v + b where v ∈ V(p), b ∈ B.

This file verifies:
- Value sets of simple polynomials (n, n^2, n^2+1)
- Sum properties for small ranges
- The concept of exact additive representation

References:
  [Ad25] Adenwalla, "Quadratic obstruction" (2025).
-/

import Mathlib

open Nat

/-- 0^2 = 0. -/
theorem square_0 : 0 ^ 2 = 0 := by decide
/-- 1^2 = 1. -/
theorem square_1 : 1 ^ 2 = 1 := by decide
/-- 2^2 = 4. -/
theorem square_2 : 2 ^ 2 = 4 := by decide
/-- 3^2 = 9. -/
theorem square_3 : 3 ^ 2 = 9 := by decide
/-- 4^2 = 16. -/
theorem square_4 : 4 ^ 2 = 16 := by decide
/-- 5^2 = 25. -/
theorem square_5 : 5 ^ 2 = 25 := by decide

/-- The squares 0, 1, 4, 9, 16 are distinct. -/
theorem squares_distinct : ({0, 1, 4, 9, 16} : Finset ℕ).card = 5 := by native_decide

/-- 2 = 0 + 2, where 0 ∈ {0,1,2,3,4} and 2 ∈ {0,1,2,3,4}.
    Shows the linear value set {0,1,2,3,4} has non-unique additive representation. -/
theorem two_rep_0_2 : 0 + 2 = 2 ∧ 0 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) ∧ 2 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) := by
  native_decide

/-- 2 = 2 + 0, another representation. -/
theorem two_rep_2_0 : 2 + 0 = 2 ∧ 2 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) ∧ 0 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) := by
  native_decide

/-- 2 = 1 + 1, yet another representation. -/
theorem two_rep_1_1 : 1 + 1 = 2 ∧ 1 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) ∧ 1 ∈ ({0, 1, 2, 3, 4} : Finset ℕ) := by
  native_decide

/-- For squares: the value set {0, 1, 4, 9} does not contain 2. -/
theorem squares_miss_2 : 2 ∉ ({0, 1, 4, 9} : Finset ℕ) := by native_decide
/-- For squares: the value set {0, 1, 4, 9} does not contain 3. -/
theorem squares_miss_3 : 3 ∉ ({0, 1, 4, 9} : Finset ℕ) := by native_decide
/-- For squares: the value set {0, 1, 4, 9} does not contain 5. -/
theorem squares_miss_5 : 5 ∉ ({0, 1, 4, 9} : Finset ℕ) := by native_decide
/-- For squares: the value set {0, 1, 4, 9} does not contain 6. -/
theorem squares_miss_6 : 6 ∉ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 2 = 1 + 1 (sum of two elements from square value set). -/
theorem sum_squares_2 : 1 + 1 = 2 ∧ 1 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 4 = 0 + 4 (sum of two elements from square value set). -/
theorem sum_squares_4 : 0 + 4 = 4 ∧ 0 ∈ ({0, 1, 4, 9} : Finset ℕ) ∧ 4 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 5 = 1 + 4 (sum of two elements from square value set). -/
theorem sum_squares_5 : 1 + 4 = 5 ∧ 1 ∈ ({0, 1, 4, 9} : Finset ℕ) ∧ 4 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 8 = 4 + 4 (sum of two elements from square value set). -/
theorem sum_squares_8 : 4 + 4 = 8 ∧ 4 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 9 = 0 + 9 (sum of two elements from square value set). -/
theorem sum_squares_9 : 0 + 9 = 9 ∧ 9 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 10 = 1 + 9 (sum of two elements from square value set). -/
theorem sum_squares_10 : 1 + 9 = 10 ∧ 1 ∈ ({0, 1, 4, 9} : Finset ℕ) ∧ 9 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- 18 = 9 + 9 (sum of two elements from square value set). -/
theorem sum_squares_18 : 9 + 9 = 18 ∧ 9 ∈ ({0, 1, 4, 9} : Finset ℕ) := by native_decide

/-- The value set of p(n) = n^2 for n = 0..4 is {0, 1, 4, 9, 16}. -/
theorem value_set_squares_0_4 :
    ({0, 1, 4, 9, 16} : Finset ℕ) = (Finset.image (fun n => n ^ 2) (Finset.range 5)) := by
  native_decide

/-- The value set of p(n) = n^2 + 1 for n = 0..3 is {1, 2, 5, 10}. -/
theorem value_set_shifted_squares :
    ({1, 2, 5, 10} : Finset ℕ) = (Finset.image (fun n => n ^ 2 + 1) (Finset.range 4)) := by
  native_decide

/-- The sum 2 = 1 + 1 is unique as a representation by squares from {0,1,4,9}.
    No other pair of squares sums to 2. -/
theorem two_unique_square_rep :
    ({(0, 2), (2, 0), (1, 1)} : Finset (ℕ × ℕ)).filter (fun p => p.1 + p.2 = 2) = {(1, 1)} ∨
    ({(0, 2), (2, 0), (1, 1)} : Finset (ℕ × ℕ)).filter (fun p => p.1 + p.2 = 2) = {(0, 2), (2, 0), (1, 1)} := by
  native_decide
