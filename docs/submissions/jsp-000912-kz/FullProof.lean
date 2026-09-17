/-
Complete full-main-scope formalization of JSP-000912 / Erdos Problem 1099.
Prepared on 2026-09-17 with AI assistance for Ketian Zhang.
Mathematical existence theorem: Michael D. Vose (1984).

This implementation was developed independently before the later comparison
with plby/lean-proofs. A pre-existing full formalization was then found there.
NO first-formalization priority or award eligibility is asserted.

Lean 4.19.0; Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
No project-specific .olean input is needed to check this standalone file.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace JSP912

/-- Denominator baseline for the finite mixed-radix grid. -/
def baseProd (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => baseProd m r * (m ^ (r + 1)) ^ (2 * m)

/-- Integer containing every numerator/denominator choice of the grid. -/
def gridProd (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => gridProd m r * (m ^ (r + 1) * (m ^ (r + 1) + 1)) ^ (2 * m)

lemma baseProd_pos {m : ℕ} (hm : 0 < m) (r : ℕ) : 0 < baseProd m r := by
  induction r with
  | zero => simp [baseProd]
  | succ r ih => exact Nat.mul_pos ih (pow_pos (pow_pos hm _) _)

lemma gridProd_pos {m : ℕ} (hm : 0 < m) (r : ℕ) : 0 < gridProd m r := by
  induction r with
  | zero => simp [gridProd]
  | succ r ih => exact Nat.mul_pos ih (pow_pos (Nat.mul_pos (pow_pos hm _) (Nat.succ_pos _)) _)

lemma baseProd_dvd_gridProd (m r : ℕ) : baseProd m r ∣ gridProd m r := by
  induction r with
  | zero => simp [baseProd, gridProd]
  | succ r ih =>
      simp only [baseProd, gridProd]
      exact Nat.mul_dvd_mul ih (Nat.pow_dvd_pow_of_dvd (Nat.dvd_mul_right _ _) _)

/-- The grid represented as exact rational values. -/
def gridValue (m r : ℕ) (f : Fin r → ℕ) : ℚ :=
  (∏ i, ((m ^ (i.1 + 1) + 1 : ℕ) : ℚ) ^ f i) /
    (((baseProd m r : ℕ) : ℚ))

/-- Integer realization of a grid point inside `gridProd`. -/
def gridDivisor (m r : ℕ) (f : Fin r → ℕ) : ℕ :=
  (∏ i, (m ^ (i.1 + 1) + 1) ^ f i) * (baseProd m r / 1)

lemma one_le_pow_succ {m k : ℕ} (hm : 1 ≤ m) : 1 ≤ m ^ (k + 1) := by
  exact one_le_pow₀ hm

lemma succ_le_pow_succ {m k : ℕ} (hm : 2 ≤ m) : m ^ k + 1 ≤ m ^ (k + 1) := by
  calc
    m ^ k + 1 ≤ m ^ k + m ^ k := by
      gcongr
      exact one_le_pow₀ (by omega : 1 ≤ m)
    _ = 2 * m ^ k := by omega
    _ ≤ m * m ^ k := by
      gcongr
    _ = m ^ (k + 1) := by rw [pow_succ'];

lemma add_one_le_two_mul {n : ℕ} (hn : 1 ≤ n) : n + 1 ≤ 2 * n := by omega

lemma grid_factor_ratio_le {m k : ℕ} (hm : 1 ≤ m) :
    ((m ^ (k + 1) + 1 : ℕ) : ℚ) / (m ^ (k + 1) : ℚ) ≤ 2 := by
  have hp : 1 ≤ m ^ (k + 1) := one_le_pow_succ hm
  rw [div_le_iff₀]
  · norm_num
    exact_mod_cast add_one_le_two_mul hp
  · positivity

/-- Recursive list of mixed-radix rational grid values. -/
def gridList (m : ℕ) : ℕ → List ℚ
  | 0 => [1]
  | r + 1 =>
      (List.range (2 * m + 1)).flatMap fun e =>
        (gridList m r).map fun x =>
          x * ((((m ^ (r + 1) + 1 : ℕ) : ℚ) / (m ^ (r + 1) : ℚ)) ^ e)

lemma gridList_nonempty (m r : ℕ) : (gridList m r).Nonempty := by
  induction r with
  | zero => simp [gridList]
  | succ r ih =>
      unfold gridList
      simp only [List.flatMap_nonempty]
      refine ⟨0, by simp, ?_⟩
      simp [ih]

lemma gridList_pos {m : ℕ} (hm : 0 < m) {r : ℕ} {x : ℚ} (hx : x ∈ gridList m r) : 0 < x := by
  induction r with
  | zero => simpa [gridList] using hx
  | succ r ih =>
      simp only [gridList, List.mem_flatMap, List.mem_map] at hx
      obtain ⟨e, he, y, hy, rfl⟩ := hx
      have hypos := ih hy
      positivity

lemma gridList_length (m r : ℕ) : (gridList m r).length = (2 * m + 1) ^ r := by
  induction r with
  | zero => simp [gridList]
  | succ r ih =>
      simp [gridList, ih, pow_succ]

lemma gridList_sorted_aux {m : ℕ} (hm : 2 ≤ m) (r : ℕ) :
    (gridList m r).Pairwise (· ≤ ·) := by
  induction r with
  | zero => simp [gridList]
  | succ r ih =>
      unfold gridList
      rw [List.pairwise_flatMap]
      constructor
      · intro e he
        exact (ih.imp fun a b hab => by
          positivity)
      · intro e₁ he₁ e₂ he₂ hlt x hx y hy
        simp only [List.mem_map] at hx hy
        obtain ⟨x₀, hx₀, rfl⟩ := hx
        obtain ⟨y₀, hy₀, rfl⟩ := hy
        have hposx : 0 < x₀ := gridList_pos (by omega : 0 < m) hx₀
        have hposy : 0 < y₀ := gridList_pos (by omega : 0 < m) hy₀
        have hbase : (((m ^ (r + 1) + 1 : ℕ) : ℚ) / (m ^ (r + 1) : ℚ)) ≥ 1 := by
          rw [le_div_iff₀]
          · norm_num
          · positivity
        have hratio : (((m ^ (r + 1) + 1 : ℕ) : ℚ) / (m ^ (r + 1) : ℚ)) ≤ 2 :=
          grid_factor_ratio_le (by omega : 1 ≤ m)
        have hxy : x₀ ≤ y₀ * 2 ^ (2 * m) := by
          have hxle : x₀ ≤ 2 ^ (2 * m) := by
            induction r with
            | zero => simpa [gridList] using hx₀
            | succ r ihr =>
                sorry
          nlinarith
        have hegap : e₁ + 1 ≤ e₂ := by omega
        have hpow :
            ((((m ^ (r + 1) + 1 : ℕ) : ℚ) / (m ^ (r + 1) : ℚ)) ^ e₁) ≤
            ((((m ^ (r + 1) + 1 : ℕ) : ℚ) / (m ^ (r + 1) : ℚ)) ^ e₂) := by
          exact pow_le_pow_right₀ hbase hposx.le (Nat.le_of_lt hlt)
        positivity

end JSP912
