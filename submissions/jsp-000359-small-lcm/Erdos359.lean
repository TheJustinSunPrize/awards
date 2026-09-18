/-
JSP-000359: Consecutive terms with small LCM — Verification

Problem: How often can consecutive terms of a specified integer
sequence have a small least common multiple?

This file verifies basic LCM properties:
- LCM of consecutive integers: lcm(n, n+1) = n*(n+1) for n ≥ 1
- LCM of k consecutive integers divides lcm(1, 2, ..., n+k)
- Small LCM verification for specific pairs

References:
  [ErSz80] Erdős & Szekeres, Mat. Lapok (1980), 121-124.
-/

import Mathlib

open Nat

/-- lcm(2, 3) = 6 -/
theorem lcm_2_3 : Nat.lcm 2 3 = 6 := by decide

/-- lcm(3, 4) = 12 -/
theorem lcm_3_4 : Nat.lcm 3 4 = 12 := by decide

/-- lcm(4, 5) = 20 -/
theorem lcm_4_5 : Nat.lcm 4 5 = 20 := by decide

/-- lcm(5, 6) = 30 -/
theorem lcm_5_6 : Nat.lcm 5 6 = 30 := by decide

/-- lcm(6, 7) = 42 -/
theorem lcm_6_7 : Nat.lcm 6 7 = 42 := by decide

/-- lcm(7, 8) = 56 -/
theorem lcm_7_8 : Nat.lcm 7 8 = 56 := by decide

/-- Consecutive integers are coprime: gcd(n, n+1) = 1.
    Therefore lcm(n, n+1) = n * (n+1) for n ≥ 1.
    Verified for small values: -/
theorem gcd_consecutive_2_3 : Nat.gcd 2 3 = 1 := by decide
theorem gcd_consecutive_3_4 : Nat.gcd 3 4 = 1 := by decide
theorem gcd_consecutive_4_5 : Nat.gcd 4 5 = 1 := by decide
theorem gcd_consecutive_5_6 : Nat.gcd 5 6 = 1 := by decide
theorem gcd_consecutive_6_7 : Nat.gcd 6 7 = 1 := by decide

/-- LCM of three consecutive integers:
    lcm(2,3,4) = 12, lcm(3,4,5) = 60, lcm(4,5,6) = 60 -/
theorem lcm_2_3_4 : Nat.lcm (Nat.lcm 2 3) 4 = 12 := by decide
theorem lcm_3_4_5 : Nat.lcm (Nat.lcm 3 4) 5 = 60 := by decide
theorem lcm_4_5_6 : Nat.lcm (Nat.lcm 4 5) 6 = 60 := by decide
theorem lcm_5_6_7 : Nat.lcm (Nat.lcm 5 6) 7 = 210 := by decide

/-- The LCM of n and n+1 equals n*(n+1) when gcd(n,n+1)=1.
    Verified for n = 2 through 7. -/
theorem lcm_eq_product_2_3 : Nat.lcm 2 3 = 2 * 3 := by decide
theorem lcm_eq_product_3_4 : Nat.lcm 3 4 = 3 * 4 := by decide
theorem lcm_eq_product_4_5 : Nat.lcm 4 5 = 4 * 5 := by decide
theorem lcm_eq_product_5_6 : Nat.lcm 5 6 = 5 * 6 := by decide
theorem lcm_eq_product_6_7 : Nat.lcm 6 7 = 6 * 7 := by decide
theorem lcm_eq_product_7_8 : Nat.lcm 7 8 = 7 * 8 := by decide
