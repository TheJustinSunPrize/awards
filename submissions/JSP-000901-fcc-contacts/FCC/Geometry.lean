import FCC.Basic
import Mathlib.Algebra.Group.Int.Even

namespace FCC

open Finset

theorem coord_sum_even {m : ℕ} (v : Vertex m) :
    Even (coord v 0 + coord v 1 + coord v 2) := by
  rcases v with ⟨a, x, y, z⟩
  fin_cases a
  · refine ⟨(x : ℤ) + y + z, ?_⟩
    norm_num [coord, cellCoord, offset, Fin.ext_iff, Matrix.cons_val_two]
    ring
  all_goals
    refine ⟨(x : ℤ) + y + z + 1, ?_⟩
    norm_num [coord, cellCoord, offset, Fin.ext_iff, Matrix.cons_val_two]
    ring

theorem coord_injective {m : ℕ} : Function.Injective (@coord m) := by
  rintro ⟨a, x, y, z⟩ ⟨b, x', y', z'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases a <;> fin_cases b <;>
    simp [coord, cellCoord, offset, Fin.ext_iff] at h0 h1 h2 ⊢ <;> omega

theorem sqDist_even {m : ℕ} (u v : Vertex m) : Even (sqDist u v) := by
  have h := (coord_sum_even u).sub (coord_sum_even v)
  have h' : Even ((coord u 0 - coord v 0) + (coord u 1 - coord v 1) +
      (coord u 2 - coord v 2)) := by
    rw [show (coord u 0 - coord v 0) + (coord u 1 - coord v 1) +
      (coord u 2 - coord v 2) =
      (coord u 0 + coord u 1 + coord u 2) - (coord v 0 + coord v 1 + coord v 2) by ring]
    exact h
  simpa [sqDist, Int.even_add, Int.even_pow] using h'

theorem sqDist_pos_of_ne {m : ℕ} {u v : Vertex m} (huv : u ≠ v) :
    0 < sqDist u v := by
  have hdiff : coord u 0 ≠ coord v 0 ∨ coord u 1 ≠ coord v 1 ∨
      coord u 2 ≠ coord v 2 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply huv
    apply coord_injective
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  rcases hdiff with h | h | h <;>
    have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
  all_goals
    unfold sqDist
    nlinarith [sq_nonneg (coord u 0 - coord v 0),
      sq_nonneg (coord u 1 - coord v 1), sq_nonneg (coord u 2 - coord v 2)]

theorem sqDist_ge_two {m : ℕ} {u v : Vertex m} (huv : u ≠ v) :
    2 ≤ sqDist u v := by
  have hp := sqDist_pos_of_ne huv
  obtain ⟨k, hk⟩ := sqDist_even u v
  omega

theorem sqDist_ne_two_of_same_offset {m : ℕ} {u v : Vertex m} (h : u.1 = v.1) :
    sqDist u v ≠ 2 := by
  have he : sqDist u v = 4 *
      ((cellCoord u 0 - cellCoord v 0) ^ 2 +
       (cellCoord u 1 - cellCoord v 1) ^ 2 +
       (cellCoord u 2 - cellCoord v 2) ^ 2) := by
    simp only [sqDist, coord, h]
    ring
  omega

theorem Contact.offset_ne {m : ℕ} {u v : Vertex m} (h : Contact u v) : u.1 ≠ v.1 := by
  intro he
  exact sqDist_ne_two_of_same_offset he h

/-- The integer squared distance is twice the actual Euclidean squared distance. -/
theorem point_dist_sq {m : ℕ} (u v : Vertex m) :
    dist (point u) (point v) ^ 2 = (sqDist u v : ℝ) / 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [point, sqDist, Fin.sum_univ_succ, Real.dist_eq, sq_abs, div_sub_div_same,
    div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

theorem point_injective {m : ℕ} : Function.Injective (@point m) := by
  intro u v h
  by_contra huv
  have hpos := sqDist_pos_of_ne huv
  have hd := point_dist_sq u v
  rw [h, dist_self] at hd
  norm_num at hd
  have hi : (0 : ℝ) < sqDist u v := by exact_mod_cast hpos
  linarith

theorem point_separated {m : ℕ} {u v : Vertex m} (huv : u ≠ v) :
    1 ≤ dist (point u) (point v) := by
  have hi : (2 : ℝ) ≤ sqDist u v := by exact_mod_cast sqDist_ge_two huv
  have hd := point_dist_sq u v
  nlinarith [dist_nonneg (x := point u) (y := point v)]

theorem point_dist_eq_one_iff {m : ℕ} (u v : Vertex m) :
    dist (point u) (point v) = 1 ↔ Contact u v := by
  have hd := point_dist_sq u v
  constructor
  · intro h
    rw [h] at hd
    have hi : (sqDist u v : ℝ) = 2 := by linarith
    exact_mod_cast hi
  · intro h
    have hi : (sqDist u v : ℝ) = 2 := by exact_mod_cast h
    rw [hi] at hd
    nlinarith [dist_nonneg (x := point u) (y := point v)]

end FCC
