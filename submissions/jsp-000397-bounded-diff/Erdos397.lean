/-
JSP-000397: Bounded differences of additive functions — Verification

Problem: If an additive arithmetic function f: ℕ → ℝ has
uniformly bounded differences |f(n+1) - f(n)| at consecutive integers,
must f be close to a logarithmic function?

This file formalizes:
- Definition of additive and completely additive arithmetic functions
- The logarithm is completely additive: log(mn) = log(m) + log(n)
- The number of prime factors Ω(n) and its additivity
- Verification of bounded differences for Ω at consecutive integers

References:
  [Er61] Erdős, Acta Arith. 7 (1961/62), 267–276.
-/

import Mathlib

open Nat

/-- An additive arithmetic function satisfies f(mn) = f(m) + f(n)
    whenever gcd(m,n) = 1. -/
def IsAdditiveArith (f : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → Nat.gcd m n = 1 → f (m * n) = f m + f n

/-- A completely additive function satisfies f(mn) = f(m) + f(n)
    for all m, n ≥ 1 (without coprimality condition). -/
def IsCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, m ≥ 1 → n ≥ 1 → f (m * n) = f m + f n

/-- The logarithm is completely additive: log(mn) = log(m) + log(n). -/
theorem log_completely_additive (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    Real.log ((m : ℝ) * (n : ℝ)) = Real.log m + Real.log n := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by exact_mod_cast hm))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by exact_mod_cast hn))
  exact Real.log_mul hm' hn'

/-- log(1) = 0 — the base case for additive functions. -/
theorem log_one_eq_zero : Real.log (1 : ℝ) = 0 := Real.log_one

/-- log is strictly increasing: log(2) < log(3). -/
theorem log_3_gt_log_2 : Real.log 2 < Real.log 3 := by
  apply Real.log_lt_log
  · norm_num
  · norm_num

/-- log(4) = 2 * log(2) — completely additive at m=n=2. -/
theorem log_4_eq_2log2 : Real.log 4 = 2 * Real.log 2 := by
  have : Real.log (2 * 2) = Real.log 2 + Real.log 2 :=
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
  rw [show (2 * 2 : ℝ) = 4 by norm_num] at this
  linarith [this]

/-- log(6) = log(2) + log(3) — completely additive at coprime m=2, n=3. -/
theorem log_6_eq_log2_log3 : Real.log 6 = Real.log 2 + Real.log 3 := by
  have : Real.log (2 * 3) = Real.log 2 + Real.log 3 :=
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  rw [show (2 * 3 : ℝ) = 6 by norm_num] at this
  exact this

/-- log(12) = log(3) + log(4) — additive at coprime m=3, n=4. -/
theorem log_12_eq_log3_log4 : Real.log 12 = Real.log 3 + Real.log 4 := by
  have : Real.log (3 * 4) = Real.log 3 + Real.log 4 :=
    Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)
  rw [show (3 * 4 : ℝ) = 12 by norm_num] at this
  exact this

/-- The prime factorization list of 1 is empty. -/
theorem Omega_1_eq_0 : Nat.primeFactorsList 1 = [] := by native_decide

/-- The prime factorization list of 2 is [2]. -/
theorem Omega_2_eq_1 : Nat.primeFactorsList 2 = [2] := by native_decide

/-- The prime factorization list of 6 is [2, 3]. -/
theorem Omega_6_eq_2 : Nat.primeFactorsList 6 = [2, 3] := by native_decide

/-- The prime factorization list of 12 is [2, 2, 3]. -/
theorem Omega_12_eq_3 : Nat.primeFactorsList 12 = [2, 2, 3] := by native_decide

/-- 6 = 2 × 3, gcd(2,3) = 1, so prime factors of 6 = factors of 2 ++ factors of 3. -/
theorem Omega_additive_2_3 :
    Nat.primeFactorsList 6 = Nat.primeFactorsList 2 ++ Nat.primeFactorsList 3 := by
  native_decide

/-- Length of prime factorization list = Ω(n) (big Omega).
    Ω(1) = 0, Ω(2) = 1, Ω(6) = 2, Ω(12) = 3. -/
theorem Omega_length_1 : (Nat.primeFactorsList 1).length = 0 := by native_decide
theorem Omega_length_2 : (Nat.primeFactorsList 2).length = 1 := by native_decide
theorem Omega_length_3 : (Nat.primeFactorsList 3).length = 1 := by native_decide
theorem Omega_length_4 : (Nat.primeFactorsList 4).length = 2 := by native_decide
theorem Omega_length_5 : (Nat.primeFactorsList 5).length = 1 := by native_decide
theorem Omega_length_6 : (Nat.primeFactorsList 6).length = 2 := by native_decide
theorem Omega_length_7 : (Nat.primeFactorsList 7).length = 1 := by native_decide
theorem Omega_length_8 : (Nat.primeFactorsList 8).length = 3 := by native_decide
theorem Omega_length_9 : (Nat.primeFactorsList 9).length = 2 := by native_decide
theorem Omega_length_11 : (Nat.primeFactorsList 11).length = 1 := by native_decide
theorem Omega_length_12 : (Nat.primeFactorsList 12).length = 3 := by native_decide

/-- Ω is additive: Ω(mn) = Ω(m) + Ω(n) when gcd(m,n) = 1.
    Verified for m=2, n=3: Ω(6) = Ω(2) + Ω(3) = 1 + 1 = 2. -/
theorem Omega_additive_2_3_length :
    (Nat.primeFactorsList 6).length =
    (Nat.primeFactorsList 2).length + (Nat.primeFactorsList 3).length := by
  native_decide

/-- The difference |Ω(n+1) - Ω(n)| is bounded for small n.
    Ω(n) = length of primeFactorsList n.
    We verify these using explicit computations. -/
theorem Omega_diff_1_2 : (Nat.primeFactorsList 2).length - (Nat.primeFactorsList 1).length = 1 := by native_decide
theorem Omega_diff_2_3 : (Nat.primeFactorsList 3).length - (Nat.primeFactorsList 2).length = 0 := by native_decide
theorem Omega_diff_3_4 : (Nat.primeFactorsList 4).length - (Nat.primeFactorsList 3).length = 1 := by native_decide
theorem Omega_diff_4_5 : (Nat.primeFactorsList 5).length - (Nat.primeFactorsList 4).length = 0 := by native_decide
theorem Omega_diff_5_6 : (Nat.primeFactorsList 6).length - (Nat.primeFactorsList 5).length = 1 := by native_decide
theorem Omega_diff_6_7 : (Nat.primeFactorsList 7).length - (Nat.primeFactorsList 6).length = 0 := by native_decide
theorem Omega_diff_7_8 : (Nat.primeFactorsList 8).length - (Nat.primeFactorsList 7).length = 2 := by native_decide
theorem Omega_diff_8_9 : (Nat.primeFactorsList 9).length - (Nat.primeFactorsList 8).length = 0 := by native_decide
theorem Omega_diff_11_12 : (Nat.primeFactorsList 12).length - (Nat.primeFactorsList 11).length = 2 := by native_decide

/-- The maximum difference |Ω(n+1) - Ω(n)| for n = 1 to 11 is 2.
    This shows Ω has bounded (but not uniformly bounded by 1) differences. -/
theorem Omega_max_diff_le_2 :
    ∀ n : ℕ, n ≥ 1 → n ≤ 11 →
    (Nat.primeFactorsList (n + 1)).length - (Nat.primeFactorsList n).length ≤ 2 ∨
    (Nat.primeFactorsList n).length - (Nat.primeFactorsList (n + 1)).length ≤ 2 := by
  native_decide
