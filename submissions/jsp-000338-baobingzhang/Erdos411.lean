import Mathlib

/-!
# Erdős Problem 411: an explicit infinite family with `g_{k+2}(n) = 2 g_k(n)`

Erdős and Graham [ErGr80, p. 81] set `g(n) = n + φ(n)` and `g_k(n) = g(g_{k-1}(n))`, and ask:
for which `n` and `r` is it true that `g_{k+r}(n) = 2 g_k(n)` for all large `k`? They note the
solutions `n = 10` and `n = 94` for `r = 2`.

Steinerberger (arXiv:2504.08023) observed that the case `r = 2` amounts to the equation
`φ(n) + φ(n + φ(n)) = n` and found the explicit solutions `n = 2^ℓ · {1, 3, 5, 7, 35, 47}`.

This file proves:
* `g_g_eq_two_mul_iff`: `g(g(m)) = 2m ↔ φ(m) + φ(m + φ(m)) = m` for every `m`, and its iterated
  form `iterate_add_two_eq_two_mul_iff`.
* `erdos_411_family`: for `ℓ ≥ 1` and `m ∈ {3, 5, 7, 35, 47}`, or `m = 1` and `ℓ ≥ 2`, the number
  `n = 2^ℓ · m` satisfies `g_{k+2}(n) = 2 g_k(n)` for every `k ≥ 0`.
* `erdos_411_family_eventually` and `erdos_411_infinite`: the Erdős–Graham property with `r = 2`
  holds for all these `n`, an infinite set.

`g_k(n)` is written `g^[k] n` (so `g^[0] n = n`).
-/

namespace Erdos411

open Nat Filter

/-- The Erdős–Graham function `g(n) = n + φ(n)`. -/
def g (n : ℕ) : ℕ := n + φ n

/-- **Steinerberger's reduction, pointwise.** `g(g(m)) = 2m` iff `φ(m) + φ(m + φ(m)) = m`. -/
theorem g_g_eq_two_mul_iff (m : ℕ) : g (g m) = 2 * m ↔ φ m + φ (m + φ m) = m := by
  unfold g
  omega

/-- **Steinerberger's reduction, iterated.** For any `n` and threshold `K`,
`g_{k+2}(n) = 2 g_k(n)` for all `k ≥ K` iff every `g_k(n)` with `k ≥ K` solves
`φ(x) + φ(x + φ(x)) = x`. -/
theorem iterate_add_two_eq_two_mul_iff (n K : ℕ) :
    (∀ k ≥ K, g^[k + 2] n = 2 * g^[k] n) ↔
      ∀ k ≥ K, φ (g^[k] n) + φ (g^[k] n + φ (g^[k] n)) = g^[k] n := by
  refine forall₂_congr fun k _ => ?_
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', g_g_eq_two_mul_iff]

/-- Multiplying an even number by `2 ^ j` multiplies its totient by `2 ^ j`. -/
theorem totient_two_pow_mul {c : ℕ} (hc : 2 ∣ c) (j : ℕ) : φ (2 ^ j * c) = 2 ^ j * φ c := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_comm (2 ^ j) 2, mul_assoc, Nat.totient_mul_of_prime_of_dvd Nat.prime_two
      (dvd_mul_of_dvd_right hc _), ih]
    ring

theorem g_two_pow_mul {c : ℕ} (hc : 2 ∣ c) (j : ℕ) : g (2 ^ j * c) = 2 ^ j * g c := by
  rw [g, g, totient_two_pow_mul hc]
  ring

/-- The family `{2^j · c : j ≥ 0, c ∈ {4, 6, 10, 14, 70, 94}}`, i.e. `2^ℓ · m` with `ℓ ≥ 1`,
`m ∈ {3, 5, 7, 35, 47}`, together with `2^ℓ`, `ℓ ≥ 2`. -/
def family : Set ℕ := {n | ∃ j, ∃ c ∈ ({4, 6, 10, 14, 70, 94} : Finset ℕ), n = 2 ^ j * c}

theorem g_four : g 4 = 6 := by decide
theorem g_six : g 6 = 8 := by decide
theorem g_ten : g 10 = 14 := by decide
theorem g_fourteen : g 14 = 20 := by decide
theorem g_seventy : g 70 = 94 := by decide
theorem g_ninetyfour : g 94 = 140 := by decide

/-- The family is `g`-invariant and every member satisfies `g(g(n)) = 2n`. -/
theorem g_mem_family_and {n : ℕ} (hn : n ∈ family) : g n ∈ family ∧ g (g n) = 2 * n := by
  obtain ⟨j, c, hc, rfl⟩ := hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨j, 6, by decide, by rw [g_two_pow_mul (by norm_num), g_four]⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_four, g_two_pow_mul (by norm_num), g_six]; ring
  · refine ⟨⟨j + 1, 4, by decide, by rw [g_two_pow_mul (by norm_num), g_six]; ring⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_six, show 2 ^ j * 8 = 2 ^ (j + 1) * 4 by ring,
      g_two_pow_mul (by norm_num), g_four]; ring
  · refine ⟨⟨j, 14, by decide, by rw [g_two_pow_mul (by norm_num), g_ten]⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_ten, g_two_pow_mul (by norm_num), g_fourteen]; ring
  · refine ⟨⟨j + 1, 10, by decide, by rw [g_two_pow_mul (by norm_num), g_fourteen]; ring⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_fourteen, show 2 ^ j * 20 = 2 ^ (j + 1) * 10 by ring,
      g_two_pow_mul (by norm_num), g_ten]; ring
  · refine ⟨⟨j, 94, by decide, by rw [g_two_pow_mul (by norm_num), g_seventy]⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_seventy, g_two_pow_mul (by norm_num), g_ninetyfour]; ring
  · refine ⟨⟨j + 1, 70, by decide, by rw [g_two_pow_mul (by norm_num), g_ninetyfour]; ring⟩, ?_⟩
    rw [g_two_pow_mul (by norm_num), g_ninetyfour, show 2 ^ j * 140 = 2 ^ (j + 1) * 70 by ring,
      g_two_pow_mul (by norm_num), g_seventy]; ring

theorem iterate_mem_family {n : ℕ} (hn : n ∈ family) (k : ℕ) : g^[k] n ∈ family := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (g_mem_family_and ih).1

/-- Every member of the family satisfies `g_{k+2}(n) = 2 g_k(n)` for all `k ≥ 0`. -/
theorem iterate_add_two_of_mem_family {n : ℕ} (hn : n ∈ family) (k : ℕ) :
    g^[k + 2] n = 2 * g^[k] n := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  exact (g_mem_family_and (iterate_mem_family hn k)).2

/-- The explicit sets of the statement describe exactly the family. -/
theorem mem_family_of {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) :
    2 ^ ℓ * m ∈ family := by
  rcases h with ⟨hℓ, hm⟩ | ⟨hℓ, rfl⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact ⟨j, 2 * m, by simp only [Finset.mem_insert, Finset.mem_singleton]; omega, by ring⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hℓ
    exact ⟨j, 4, by decide, by ring⟩

/-- **Erdős Problem 411, explicit family (Steinerberger).** For `ℓ ≥ 1` and
`m ∈ {3, 5, 7, 35, 47}`, and for `m = 1` with `ℓ ≥ 2`, the number `n = 2^ℓ · m` satisfies
`g_{k+2}(n) = 2 g_k(n)` for every `k ≥ 0`. -/
theorem erdos_411_family {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) (k : ℕ) :
    g^[k + 2] (2 ^ ℓ * m) = 2 * g^[k] (2 ^ ℓ * m) :=
  iterate_add_two_of_mem_family (mem_family_of h) k

/-- Steinerberger's explicit solutions of `φ(n) + φ(n + φ(n)) = n`. -/
theorem totient_add_totient_eq_of {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) :
    φ (2 ^ ℓ * m) + φ (2 ^ ℓ * m + φ (2 ^ ℓ * m)) = 2 ^ ℓ * m :=
  (g_g_eq_two_mul_iff _).1 (erdos_411_family h 0)

/-- **Erdős Problem 411, in the shape of the question.** For each such `n = 2^ℓ · m`, there is
`r` (namely `r = 2`) with `g_{k+r}(n) = 2 g_k(n)` for all large `k`. -/
theorem erdos_411_family_eventually {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) :
    ∃ r ≥ 1, ∀ᶠ k in atTop, g^[k + r] (2 ^ ℓ * m) = 2 * g^[k] (2 ^ ℓ * m) :=
  ⟨2, by norm_num, Eventually.of_forall (erdos_411_family h)⟩

/-- The set of `n` with `g_{k+2}(n) = 2 g_k(n)` for all large `k` is infinite. -/
theorem erdos_411_infinite :
    {n : ℕ | ∀ᶠ k in atTop, g^[k + 2] n = 2 * g^[k] n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 2 ^ (j + 1) * 5) ?_ ?_
  · intro a b hab
    simpa using hab
  · intro j
    exact Eventually.of_forall (erdos_411_family (Or.inl ⟨by omega, by decide⟩))

/-- The two solutions noted by Erdős and Graham, `10 = 2 · 5` and `94 = 2 · 47`, are members. -/
example : ∀ k, g^[k + 2] 10 = 2 * g^[k] 10 := erdos_411_family (ℓ := 1) (m := 5) (Or.inl ⟨le_rfl, by decide⟩)
example : ∀ k, g^[k + 2] 94 = 2 * g^[k] 94 := erdos_411_family (ℓ := 1) (m := 47) (Or.inl ⟨le_rfl, by decide⟩)

end Erdos411
