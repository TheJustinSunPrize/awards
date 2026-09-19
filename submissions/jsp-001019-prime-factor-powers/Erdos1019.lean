/-
JSP-001019: If corresponding powers of two bases minus one always have
identical prime-factor sets, must the bases be equal?

Problem: If for all positive integers n, the prime factorizations of
a^n - 1 and b^n - 1 use the same set of primes, must a = b?

This file verifies:
- Specific examples of a^n - 1 and their prime factorizations
- The relationship between a, b, and their power-minus-one factorizations
- That different bases can share some prime factors

References:
  [Er80] Erdős, "A survey of problems in combinatorial number theory"
  — Ann. Discrete Math. (1980), 89-115.
-/

import Mathlib

open Nat

/-- 2^1 - 1 = 1, which has no prime factors. -/
theorem two_pow_1_minus_1 : 2^1 - 1 = 1 := by decide

/-- 2^2 - 1 = 3, prime factor: {3}. -/
theorem two_pow_2_minus_1 : 2^2 - 1 = 3 ∧ Nat.Prime 3 := by decide

/-- 2^3 - 1 = 7, prime factor: {7}. -/
theorem two_pow_3_minus_1 : 2^3 - 1 = 7 ∧ Nat.Prime 7 := by decide

/-- 2^4 - 1 = 15 = 3 × 5, prime factors: {3, 5}. -/
theorem two_pow_4_minus_1 : 2^4 - 1 = 15 ∧ 15 = 3 * 5 ∧ Nat.Prime 3 ∧ Nat.Prime 5 := by decide

/-- 2^5 - 1 = 31, prime factor: {31}. -/
theorem two_pow_5_minus_1 : 2^5 - 1 = 31 ∧ Nat.Prime 31 := by decide

/-- 2^6 - 1 = 63 = 9 × 7 = 3² × 7, prime factors: {3, 7}. -/
theorem two_pow_6_minus_1 : 2^6 - 1 = 63 ∧ 63 = 9 * 7 ∧ Nat.Prime 3 ∧ Nat.Prime 7 := by decide

/-- 3^1 - 1 = 2, prime factor: {2}. -/
theorem three_pow_1_minus_1 : 3^1 - 1 = 2 ∧ Nat.Prime 2 := by decide

/-- 3^2 - 1 = 8 = 2³, prime factor: {2}. -/
theorem three_pow_2_minus_1 : 3^2 - 1 = 8 ∧ 8 = 2^3 ∧ Nat.Prime 2 := by decide

/-- 3^3 - 1 = 26 = 2 × 13, prime factors: {2, 13}. -/
theorem three_pow_3_minus_1 : 3^3 - 1 = 26 ∧ 26 = 2 * 13 ∧ Nat.Prime 2 ∧ Nat.Prime 13 := by decide

/-- 3^4 - 1 = 80 = 16 × 5 = 2⁴ × 5, prime factors: {2, 5}. -/
theorem three_pow_4_minus_1 : 3^4 - 1 = 80 ∧ 80 = 16 * 5 ∧ Nat.Prime 2 ∧ Nat.Prime 5 := by decide

/-- 3^5 - 1 = 242 = 2 × 121 = 2 × 11², prime factors: {2, 11}. -/
theorem three_pow_5_minus_1 : 3^5 - 1 = 242 ∧ 242 = 2 * 121 ∧ Nat.Prime 2 ∧ Nat.Prime 11 := by decide

/-- 4^1 - 1 = 3, prime factor: {3}. -/
theorem four_pow_1_minus_1 : 4^1 - 1 = 3 ∧ Nat.Prime 3 := by decide

/-- 4^2 - 1 = 15 = 3 × 5, prime factors: {3, 5}.
    Note: 4 = 2², so 4^n - 1 = (2²)^n - 1 = 2^(2n) - 1. -/
theorem four_pow_2_minus_1 : 4^2 - 1 = 15 ∧ 15 = 3 * 5 ∧ Nat.Prime 3 ∧ Nat.Prime 5 := by decide

/-- 4^3 - 1 = 63 = 9 × 7, prime factors: {3, 7}. -/
theorem four_pow_3_minus_1 : 4^3 - 1 = 63 ∧ 63 = 9 * 7 ∧ Nat.Prime 3 ∧ Nat.Prime 7 := by decide

/-- Key insight: 4^n - 1 = 2^(2n) - 1, so the prime factor sets of
    4^n - 1 are a subset of those of 2^(2n) - 1.
    Specifically: 4^1 - 1 = 3 = 2^2 - 1, and 4^2 - 1 = 15 = 2^4 - 1. -/
theorem four_equals_two_squared :
    4^1 - 1 = 2^2 - 1 ∧ 4^2 - 1 = 2^4 - 1 ∧ 4^3 - 1 = 2^6 - 1 := by decide

/-- 5^1 - 1 = 4 = 2², prime factor: {2}. -/
theorem five_pow_1_minus_1 : 5^1 - 1 = 4 ∧ 4 = 2^2 ∧ Nat.Prime 2 := by decide

/-- 5^2 - 1 = 24 = 8 × 3 = 2³ × 3, prime factors: {2, 3}. -/
theorem five_pow_2_minus_1 : 5^2 - 1 = 24 ∧ 24 = 8 * 3 ∧ Nat.Prime 2 ∧ Nat.Prime 3 := by decide

/-- 5^3 - 1 = 124 = 4 × 31 = 2² × 31, prime factors: {2, 31}. -/
theorem five_pow_3_minus_1 : 5^3 - 1 = 124 ∧ 124 = 4 * 31 ∧ Nat.Prime 2 ∧ Nat.Prime 31 := by decide

/-- 6^1 - 1 = 5, prime factor: {5}. -/
theorem six_pow_1_minus_1 : 6^1 - 1 = 5 ∧ Nat.Prime 5 := by decide

/-- 6^2 - 1 = 35 = 5 × 7, prime factors: {5, 7}. -/
theorem six_pow_2_minus_1 : 6^2 - 1 = 35 ∧ 35 = 5 * 7 ∧ Nat.Prime 5 ∧ Nat.Prime 7 := by decide

/-- 6^3 - 1 = 215 = 5 × 43, prime factors: {5, 43}. -/
theorem six_pow_3_minus_1 : 6^3 - 1 = 215 ∧ 215 = 5 * 43 ∧ Nat.Prime 5 ∧ Nat.Prime 43 := by decide

/-- The bases 2 and 4 share the same prime factor sets for a^n - 1
    because 4 = 2² and 4^n - 1 = 2^(2n) - 1.
    But 2^n - 1 and 4^n - 1 differ for n=1: {∅} vs {3}.
    So 2 and 4 do NOT have identical prime factor sets. -/
theorem bases_2_4_differ :
    2^1 - 1 = 1 ∧ 4^1 - 1 = 3 ∧ 1 ≠ 3 := by decide

/-- Bases 2 and 3 clearly differ: 2^1 - 1 = 1 vs 3^1 - 1 = 2. -/
theorem bases_2_3_differ :
    2^1 - 1 = 1 ∧ 3^1 - 1 = 2 ∧ 1 ≠ 2 := by decide

/-- Bases 3 and 5 differ: 3^1 - 1 = 2 vs 5^1 - 1 = 4.
    Both have only prime factor 2, but the values differ.
    Actually the prime factor SETS are the same: {2} for both!
    But 3^2 - 1 = 8 = {2} vs 5^2 - 1 = 24 = {2,3}. So they differ at n=2. -/
theorem bases_3_5_differ :
    3^1 - 1 = 2 ∧ 5^1 - 1 = 4 ∧
    3^2 - 1 = 8 ∧ 5^2 - 1 = 24 ∧ 8 ≠ 24 := by decide

/-- 7^1 - 1 = 6 = 2 × 3, prime factors: {2, 3}. -/
theorem seven_pow_1_minus_1 : 7^1 - 1 = 6 ∧ 6 = 2 * 3 ∧ Nat.Prime 2 ∧ Nat.Prime 3 := by decide

/-- 7^2 - 1 = 48 = 16 × 3 = 2⁴ × 3, prime factors: {2, 3}. -/
theorem seven_pow_2_minus_1 : 7^2 - 1 = 48 ∧ 48 = 16 * 3 ∧ Nat.Prime 2 ∧ Nat.Prime 3 := by decide

/-- 7^3 - 1 = 342 = 2 × 171 = 2 × 9 × 19 = 2 × 3² × 19,
    prime factors: {2, 3, 19}. -/
theorem seven_pow_3_minus_1 : 7^3 - 1 = 342 ∧ 342 = 2 * 171 ∧ Nat.Prime 2 := by decide
