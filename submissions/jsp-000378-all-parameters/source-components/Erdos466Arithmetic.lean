import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace Erdos466General

/-- Uniform interval estimate for distances between separated points on a parabola.
The integer-base construction can apply this to every pair, without discarding a tail. -/
theorem parabola_distance_interval (δ u v q : ℝ)
    (hd0 : 0 ≤ δ) (hd : δ < 1 / 2) (hu : 1 ≤ u)
    (hq : 4 ≤ q) (hchoose : 4 < (1 - 2 * δ) * q) (hv : q * u ≤ v) :
    let a := v ^ 2 - u ^ 2
    a + δ < Real.sqrt (a ^ 2 + (v - u) ^ 2) ∧
      Real.sqrt (a ^ 2 + (v - u) ^ 2) < a + 1 / 2 := by
  dsimp only
  have hu0 : 0 < u := by linarith
  have hcoef : 0 < 1 - 2 * δ := by linarith
  have hv4 : 4 * u ≤ v :=
    (mul_le_mul_of_nonneg_right hq hu0.le).trans hv
  have hvu : 1 ≤ v - u := by linarith
  have hv0 : 0 < v := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hv hcoef.le
  have hchosen := mul_lt_mul_of_pos_right hchoose hu0
  have hfour : 4 * u < (1 - 2 * δ) * v := by nlinarith only [hscaled, hchosen]
  have hcoefu := mul_pos hcoef hu0
  have hlinear : 1 < (1 - 2 * δ) * v - (1 + 2 * δ) * u := by
    nlinarith only [hfour, hcoefu, hu]
  have hproduct :
      1 < (v - u) * ((1 - 2 * δ) * v - (1 + 2 * δ) * u) := by
    calc
      1 < (1 - 2 * δ) * v - (1 + 2 * δ) * u := hlinear
      _ ≤ (v - u) * ((1 - 2 * δ) * v - (1 + 2 * δ) * u) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hvu)
          (show 0 ≤ (1 - 2 * δ) * v - (1 + 2 * δ) * u by linarith)]
  have hδsq : δ ^ 2 < 1 := by nlinarith only [hd0, hd]
  have ha : 0 < v ^ 2 - u ^ 2 := by
    nlinarith only [mul_pos (show 0 < v - u by linarith) (show 0 < v + u by linarith)]
  have hleftsq : (v ^ 2 - u ^ 2 + δ) ^ 2 <
      (v ^ 2 - u ^ 2) ^ 2 + (v - u) ^ 2 := by
    nlinarith only [hproduct, hδsq]
  have hrightsq : (v ^ 2 - u ^ 2) ^ 2 + (v - u) ^ 2 <
      (v ^ 2 - u ^ 2 + 1 / 2) ^ 2 := by
    nlinarith only [mul_pos hu0 (show 0 < v - u by linarith)]
  exact ⟨Real.lt_sqrt_of_sq_lt hleftsq,
    (Real.sqrt_lt' (by linarith : 0 < v ^ 2 - u ^ 2 + 1 / 2)).2 hrightsq⟩

#print axioms parabola_distance_interval

end Erdos466General
