/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license. This file has been modified.

Definitions and elementary bridges for an all-parameter extension of
Graham's construction for Erdős Problem 466 / JSP-000378.

The nearest-integer convention and the interval bridge follow the public
formalization in plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, ErdosProblems/Erdos466.lean.
That source credits Ronald Graham (mathematics), the Formal Conjectures
Authors, and Codex / GPT-5.6 Sol (formalization).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Metric Set Filter
open scoped Topology

namespace Erdos466General
noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := abs_sub_round x

lemma distToInt_le (x : ℝ) (z : ℤ) : distToInt x ≤ |x - (z : ℝ)| :=
  round_le x z

lemma distToInt_gt_of_between {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x) (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToInt x := by
  rw [distToInt]
  let z : ℤ := round x
  have hz : z ≤ a ∨ a + 1 ≤ z := by omega
  rcases hz with hza | haz
  · have hza' : (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc
      δ < x - (z : ℝ) := by linarith
      _ ≤ |x - (z : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast haz
    calc
      δ < -(x - (z : ℝ)) := by linarith
      _ ≤ |x - (z : ℝ)| := neg_le_abs _

/-- At the endpoint, twice the real number is an odd integer. -/
lemma half_le_distToInt_iff (x : ℝ) :
    1 / 2 ≤ distToInt x ↔ ∃ z : ℤ, 2 * x = (2 * z + 1 : ℤ) := by
  rw [distToInt, abs_sub_round_eq_min, le_min_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨⌊x⌋, ?_⟩
    simp only [Int.fract] at h₁ h₂
    push_cast
    linarith
  · rintro ⟨z, hz⟩
    have hx : x = (z : ℝ) + 1 / 2 := by push_cast at hz; linarith
    rw [hx, Int.fract_intCast_add]
    norm_num [Int.fract]

def point (q m : ℕ) : Plane := !₂[(q : ℝ) ^ m, ((q : ℝ) ^ m) ^ 2]

@[simp] lemma point_zero (q m : ℕ) : point q m 0 = (q : ℝ) ^ m := by
  simp [point]

@[simp] lemma point_one (q m : ℕ) : point q m 1 = ((q : ℝ) ^ m) ^ 2 := by
  simp [point]

lemma point_injective {q : ℕ} (hq : 2 ≤ q) : Function.Injective (point q) := by
  intro i j hij
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hc := congrArg (fun p : Plane ↦ p 0) hij
  exact (pow_right_strictMono₀ hqR).injective (by simpa using hc)

lemma point_dist (q i j : ℕ) :
    dist (point q i) (point q j) =
      Real.sqrt ((((q : ℝ) ^ j) ^ 2 - ((q : ℝ) ^ i) ^ 2) ^ 2 +
        ((q : ℝ) ^ j - (q : ℝ) ^ i) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, point_zero, point_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  congr 1
  ring

lemma plane_dist_sq (p r : Plane) :
    dist p r ^ 2 = (p 0 - r 0) ^ 2 + (p 1 - r 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

end
end Erdos466General
