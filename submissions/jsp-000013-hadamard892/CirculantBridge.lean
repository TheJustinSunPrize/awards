import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Tactic.Abel

/-!
Circulants and reflection for the Goethals--Seidel construction.
The convention throughout is `circulant a r c = a (r-c)` and
`corr a t = sum_x a x * a (x+t)`. The reflection has zero offset.
All identities are generic over a finite additive commutative index group.
-/
namespace Hadamard892

open Matrix

/-- The permutation matrix of the involution x ↦ -x. -/
def reflection (I : Type*) [DecidableEq I] [AddGroup I] : Matrix I I ℤ :=
  fun r c => if c = -r then 1 else 0

/-- Periodic autocorrelation, with a positive shift in the second factor. -/
def corr {I : Type*} [Fintype I] [Add I] (a : I → ℤ) (t : I) : ℤ :=
  ∑ x, a x * a (x + t)

section
variable {I : Type*} [Fintype I] [DecidableEq I] [AddCommGroup I]

omit [Fintype I] in
lemma reflection_transpose : (reflection I)ᵀ = reflection I := by
  ext r c
  have he : (r = -c) ↔ (c = -r) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp only [Matrix.transpose_apply, reflection, he]

lemma reflection_mul_apply (M : Matrix I I ℤ) (r c : I) :
    (reflection I * M) r c = M (-r) c := by
  simp [Matrix.mul_apply, reflection, ite_mul]

lemma mul_reflection_apply (M : Matrix I I ℤ) (r c : I) :
    (M * reflection I) r c = M r (-c) := by
  have he (j : I) : (c = -j) ↔ (j = -c) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp [Matrix.mul_apply, reflection, he, mul_ite]

lemma reflection_mul_self : reflection I * reflection I = 1 := by
  ext r c
  rw [reflection_mul_apply]
  simp [reflection, Matrix.one_apply, eq_comm]

lemma reflection_mul_circulant (a : I → ℤ) :
    reflection I * Matrix.circulant a = (Matrix.circulant a)ᵀ * reflection I := by
  ext r c
  simp only [reflection_mul_apply, mul_reflection_apply,
    Matrix.transpose_apply, Matrix.circulant_apply]
  congr 1
  abel

omit [DecidableEq I] in
lemma circulant_commute (a b : I → ℤ) :
    Matrix.circulant a * Matrix.circulant b =
      Matrix.circulant b * Matrix.circulant a :=
  Matrix.circulant_mul_comm a b

omit [DecidableEq I] in
lemma circulant_transpose_commute (a b : I → ℤ) :
    Matrix.circulant a * (Matrix.circulant b)ᵀ =
      (Matrix.circulant b)ᵀ * Matrix.circulant a := by
  rw [Matrix.transpose_circulant]
  exact Matrix.circulant_mul_comm a (fun i => b (-i))

omit [DecidableEq I] in
lemma circulant_transposes_commute (a b : I → ℤ) :
    (Matrix.circulant a)ᵀ * (Matrix.circulant b)ᵀ =
      (Matrix.circulant b)ᵀ * (Matrix.circulant a)ᵀ := by
  rw [Matrix.transpose_circulant, Matrix.transpose_circulant]
  exact Matrix.circulant_mul_comm (fun i => a (-i)) (fun i => b (-i))

lemma circulant_mul_reflection_apply (a : I → ℤ) (r c : I) :
    (Matrix.circulant a * reflection I) r c = a (r + c) := by
  simp [mul_reflection_apply, Matrix.circulant_apply]

lemma transpose_circulant_mul_reflection_apply (a : I → ℤ) (r c : I) :
    ((Matrix.circulant a)ᵀ * reflection I) r c = a (-(r + c)) := by
  rw [mul_reflection_apply, Matrix.transpose_apply, Matrix.circulant_apply]
  congr 1
  abel

omit [DecidableEq I] in
lemma circulant_gram_entry (a : I → ℤ) (r s : I) :
    (Matrix.circulant a * (Matrix.circulant a)ᵀ) r s = corr a (s - r) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.circulant_apply, corr]
  refine Fintype.sum_equiv (Equiv.subLeft r) _ _ ?_
  intro c
  simp only [Equiv.subLeft_apply]
  congr 2
  abel

/-- The scalar autocorrelations supply the sum of the four circulant Gram matrices. -/
lemma correlations_sum_gram (a : Fin 4 → I → ℤ) (σ : ℤ)
    (h : ∀ t : I, (∑ i, corr (a i) t) = if t = 0 then σ else 0) :
    (∑ i, Matrix.circulant (a i) * (Matrix.circulant (a i))ᵀ) =
      σ • (1 : Matrix I I ℤ) := by
  ext r s
  simp only [Matrix.sum_apply, circulant_gram_entry, h,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hrs : r = s
  · simp [hrs]
  · have hsr : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
    simp [hrs, hsr]

omit [Fintype I] [DecidableEq I] in
lemma circulant_entry_signs (a : I → ℤ) (ha : ∀ x, a x = 1 ∨ a x = -1)
    (r c : I) : Matrix.circulant a r c = 1 ∨ Matrix.circulant a r c = -1 :=
  ha (r - c)

lemma circulant_reflection_entry_signs (a : I → ℤ) (ha : ∀ x, a x = 1 ∨ a x = -1)
    (r c : I) : (Matrix.circulant a * reflection I) r c = 1 ∨
      (Matrix.circulant a * reflection I) r c = -1 := by
  rw [circulant_mul_reflection_apply]
  exact ha (r + c)

lemma transpose_circulant_reflection_entry_signs (a : I → ℤ)
    (ha : ∀ x, a x = 1 ∨ a x = -1) (r c : I) :
    ((Matrix.circulant a)ᵀ * reflection I) r c = 1 ∨
      ((Matrix.circulant a)ᵀ * reflection I) r c = -1 := by
  rw [transpose_circulant_mul_reflection_apply]
  exact ha (-(r + c))

end
end Hadamard892
