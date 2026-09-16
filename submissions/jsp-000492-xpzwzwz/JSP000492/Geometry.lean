import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace JSP000492

abbrev E := EuclideanSpace ℝ (Fin 3)

noncomputable def normalize (v : E) : E := ‖v‖⁻¹ • v

noncomputable def point (x y : ℝ) : E := normalize !₂[x, y, 1]

noncomputable def line (a b : ℝ) : E := normalize !₂[a, -1, b]

private lemma point_raw_ne_zero (x y : ℝ) : (!₂[x, y, 1] : E) ≠ 0 := by
  intro h
  have := congrArg (fun v : E => v 2) h
  norm_num at this

private lemma line_raw_ne_zero (a b : ℝ) : (!₂[a, -1, b] : E) ≠ 0 := by
  intro h
  have := congrArg (fun v : E => v 1) h
  norm_num at this

private lemma normalize_norm (v : E) (hv : v ≠ 0) : ‖normalize v‖ = 1 := by
  simp [normalize, norm_smul, norm_ne_zero_iff.mpr hv]

theorem point_norm (x y : ℝ) : ‖point x y‖ = 1 :=
  normalize_norm _ (point_raw_ne_zero x y)

theorem line_norm (a b : ℝ) : ‖line a b‖ = 1 :=
  normalize_norm _ (line_raw_ne_zero a b)

theorem point_injective : Function.Injective (fun p : ℝ × ℝ => point p.1 p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h0 := congrArg (fun v : E => v 0) h
  have h1 := congrArg (fun v : E => v 1) h
  have h2 := congrArg (fun v : E => v 2) h
  simp [point, normalize] at h0 h1 h2
  rw [← h2] at h0 h1
  have hn : ‖(!₂[x, y, 1] : E)‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr (point_raw_ne_zero x y))
  exact Prod.ext (mul_left_cancel₀ hn h0) (mul_left_cancel₀ hn h1)

theorem line_injective : Function.Injective (fun p : ℝ × ℝ => line p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := congrArg (fun v : E => v 0) h
  have h1 := congrArg (fun v : E => v 1) h
  have h2 := congrArg (fun v : E => v 2) h
  simp [line, normalize] at h0 h1 h2
  rw [← h1] at h0 h2
  have hn : ‖(!₂[a, -1, b] : E)‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr (line_raw_ne_zero a b))
  exact Prod.ext (mul_left_cancel₀ hn h0) (mul_left_cancel₀ hn h2)

theorem point_ne_line (x y a b : ℝ) (hy : 0 ≤ y) : point x y ≠ line a b := by
  intro h
  have h1 := congrArg (fun v : E => v 1) h
  simp [point, line, normalize] at h1
  have hp : 0 ≤ ‖(!₂[x, y, 1] : E)‖⁻¹ * y := mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hy
  have hl : 0 < ‖(!₂[a, -1, b] : E)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (line_raw_ne_zero a b))
  linarith

theorem incidence_dist (x y a b : ℝ) (h : y = a * x + b) :
    dist (point x y) (line a b) = Real.sqrt 2 := by
  have hi : inner ℝ (point x y) (line a b) = 0 := by
    simp [point, line, normalize, inner_smul_left, inner_smul_right, PiLp.inner_apply,
      Fin.sum_univ_succ, h]
  have hs := norm_sub_sq_real (point x y) (line a b)
  rw [point_norm, line_norm, hi] at hs
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (point x y - line a b), Real.sqrt_nonneg (2 : ℝ)]

end JSP000492
