/-!
# JSP-000301: Consecutive powerful numbers need not be squares

Golomb's counterexample: 12167 = 23^3 and 12168 = 2^3 · 3^2 · 13^2 are consecutive
powerful numbers, neither of which is a perfect square.

A number n is powerful if for every prime p | n, p^2 | n.
-/

import Mathlib

open Nat

/-- A number is powerful if every prime divisor p satisfies p^2 | n -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- 12167 = 23^3 -/
theorem eq_12167 : 12167 = 23^3 := by norm_num

/-- 23 is prime -/
theorem prime_23 : Nat.Prime 23 := by decide

/-- 12167 is powerful: only prime divisor is 23, and 23^2 | 23^3 -/
theorem powerful_12167 : IsPowerful 12167 := by
  intro p hp hpd
  have h : 12167 = 23^3 := by norm_num
  rw [h] at hpd
  have hp_dvd_23 : p ∣ 23 := hp.dvd_of_dvd_pow hpd
  have hp_eq_23 : p = 23 := (Nat.prime_dvd_prime_iff_eq hp prime_23).mp hp_dvd_23
  rw [hp_eq_23]
  use 23
  norm_num

/-- 12168 = 2^3 * 3^2 * 13^2 -/
theorem eq_12168 : 12168 = 2^3 * 3^2 * 13^2 := by norm_num

/-- 12167 and 12168 are consecutive -/
theorem consecutive_12167_12168 : 12168 - 12167 = 1 := by norm_num

/-- 12167 is not a perfect square: 110^2 = 12100 < 12167 < 12100+221 < 121^2 = 14641 -/
theorem not_square_12167 : ¬ (∃ m : ℕ, m^2 = 12167) := by
  intro ⟨m, hm⟩
  have h110 : 110^2 = 12100 := by norm_num
  have h111 : 111^2 = 12321 := by norm_num
  have : 110 < m := by
    by_contra h
    have : m ≤ 110 := not_lt.mp h
    have : m^2 ≤ 110^2 := Nat.mul_le_mul this this
    rw [hm, h110] at this
    norm_num at this
  have : m ≤ 110 := by
    by_contra h
    have : 111 ≤ m := Nat.le_of_lt h
    have : 111^2 ≤ m^2 := Nat.mul_le_mul this this
    rw [hm] at this
    rw [h111] at this
    norm_num at this
  rw [hm] at *
  norm_num at this

/-- 12168 is not a perfect square: 110^2 = 12100 < 12168 < 111^2 = 12321 -/
theorem not_square_12168 : ¬ (∃ m : ℕ, m^2 = 12168) := by
  intro ⟨m, hm⟩
  have h110 : 110^2 = 12100 := by norm_num
  have h111 : 111^2 = 12321 := by norm_num
  have : 110 < m := by
    by_contra h
    have : m ≤ 110 := not_lt.mp h
    have : m^2 ≤ 12100 := Nat.mul_le_mul this this
    rw [hm] at this
    norm_num at this
  have : m ≤ 110 := by
    by_contra h
    have : 111 ≤ m := Nat.le_of_lt h
    have : 12321 ≤ m^2 := Nat.mul_le_mul this this
    rw [hm] at this
    norm_num at this
  rw [hm] at *
  norm_num at this
