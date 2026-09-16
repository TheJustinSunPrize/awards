import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace Erdos466General

/-- Determinant of twice the Gram matrix of three vectors, expressed in the
six squared pairwise distances from four points. -/
def sixDistanceGramDet {R : Type*} [CommRing R] (A B C D E F : R) : R :=
  8 * A * B * C + 2 * (A + B - D) * (A + C - E) * (B + C - F)
    - 2 * A * (B + C - F) ^ 2
    - 2 * B * (A + C - E) ^ 2
    - 2 * C * (A + B - D) ^ 2

/-- Every odd integer has square congruent to one modulo eight. -/
theorem odd_sq_emod_eight (n : ℤ) (hn : Odd n) : n ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ := hn
  have hr : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr <;> norm_num [pow_two, Int.mul_emod, hr]

/-- The determinant obstruction when all six squared distances are one modulo eight. -/
theorem sixDistanceGramDet_emod_eight (A B C D E F : ℤ)
    (hA : A % 8 = 1) (hB : B % 8 = 1) (hC : C % 8 = 1)
    (hD : D % 8 = 1) (hE : E % 8 = 1) (hF : F % 8 = 1) :
    sixDistanceGramDet A B C D E F % 8 = 4 := by
  norm_num [sixDistanceGramDet, Int.add_emod, Int.sub_emod, Int.mul_emod,
    pow_two, hA, hB, hC, hD, hE, hF]

theorem sixDistanceGramDet_ne_zero_of_mod_eight (A B C D E F : ℤ)
    (hA : A % 8 = 1) (hB : B % 8 = 1) (hC : C % 8 = 1)
    (hD : D % 8 = 1) (hE : E % 8 = 1) (hF : F % 8 = 1) :
    sixDistanceGramDet A B C D E F ≠ 0 := by
  have h := sixDistanceGramDet_emod_eight A B C D E F hA hB hC hD hE hF
  intro hzero
  rw [hzero] at h
  norm_num at h

/-- Four points with odd integral mutual distances would have a nonzero Gram determinant. -/
theorem sixDistanceGramDet_ne_zero_of_odd (a b c d e f : ℤ)
    (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (hd : Odd d) (he : Odd e) (hf : Odd f) :
    sixDistanceGramDet (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) ≠ 0 :=
  sixDistanceGramDet_ne_zero_of_mod_eight _ _ _ _ _ _
    (odd_sq_emod_eight a ha) (odd_sq_emod_eight b hb) (odd_sq_emod_eight c hc)
    (odd_sq_emod_eight d hd) (odd_sq_emod_eight e he) (odd_sq_emod_eight f hf)

/-- Any three vectors in the real plane have zero Gram determinant.  This is
the coordinate identity needed to exclude four points with odd integral distances. -/
theorem sixDistanceGramDet_plane (u₁ u₂ v₁ v₂ w₁ w₂ : ℝ) :
    sixDistanceGramDet
      (u₁ ^ 2 + u₂ ^ 2) (v₁ ^ 2 + v₂ ^ 2) (w₁ ^ 2 + w₂ ^ 2)
      ((u₁ - v₁) ^ 2 + (u₂ - v₂) ^ 2)
      ((u₁ - w₁) ^ 2 + (u₂ - w₂) ^ 2)
      ((v₁ - w₁) ^ 2 + (v₂ - w₂) ^ 2) = 0 := by
  unfold sixDistanceGramDet
  ring

@[simp] theorem sixDistanceGramDet_intCast (A B C D E F : ℤ) :
    ((sixDistanceGramDet A B C D E F : ℤ) : ℝ) =
      sixDistanceGramDet (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (E : ℝ) (F : ℝ) := by
  simp [sixDistanceGramDet]

#print axioms sixDistanceGramDet_ne_zero_of_odd
#print axioms sixDistanceGramDet_plane

end Erdos466General
