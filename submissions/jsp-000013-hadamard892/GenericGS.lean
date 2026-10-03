import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
The classical Goethals–Seidel block construction.
This file proves only generic matrix algebra. Concrete circulant, sign and
correlation hypotheses are discharged in separate modules.
-/

-- Disable optional simplifier procedures; all rewrites still produce kernel-checked proofs.
-- Lean 4.34.0 otherwise emits recoverable Expr.appArg!/appFn! diagnostics here.
set_option simprocs false

open scoped BigOperators Matrix

namespace Hadamard892

variable {I : Type*} [Fintype I] [DecidableEq I]

def gsBlocks (X : Fin 4 → Matrix I I ℤ) (J : Matrix I I ℤ) :
    Matrix (Fin 4) (Fin 4) (Matrix I I ℤ) :=
  ![![X 0, X 1 * J, X 2 * J, X 3 * J],
    ![-(X 1 * J), X 0, -((X 3)ᵀ * J), (X 2)ᵀ * J],
    ![-(X 2 * J), (X 3)ᵀ * J, X 0, -((X 1)ᵀ * J)],
    ![-(X 3 * J), -((X 2)ᵀ * J), (X 1)ᵀ * J, X 0]]

def gsMatrix (X : Fin 4 → Matrix I I ℤ) (J : Matrix I I ℤ) :
    Matrix (Fin 4 × I) (Fin 4 × I) ℤ :=
  fun p q => gsBlocks X J p.1 q.1 p.2 q.2

lemma gs_reverse_transpose (X : Fin 4 → Matrix I I ℤ) (J : Matrix I I ℤ)
    (hJJ : J * J = 1)
    (hrev : ∀ i, J * X i = (X i)ᵀ * J) (i : Fin 4) :
    J * (X i)ᵀ = X i * J := by
  calc
    J * (X i)ᵀ = (J * ((X i)ᵀ * J)) * J := by
      simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    _ = (J * (J * X i)) * J := by rw [← hrev i]
    _ = X i * J := by rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]

set_option linter.unusedSimpArgs false in
/-- All sixteen block row-Gram equations of the classical array. -/
theorem gsBlocks_rowGram
    (X : Fin 4 → Matrix I I ℤ) (J : Matrix I I ℤ)
    (hJt : Jᵀ = J) (hJJ : J * J = 1)
    (hrev : ∀ i, J * X i = (X i)ᵀ * J)
    (hcomm : ∀ i j, X i * X j = X j * X i)
    (hmixed : ∀ i j, X i * (X j)ᵀ = (X j)ᵀ * X i)
    (i j : Fin 4) :
    (∑ k : Fin 4, gsBlocks X J i k * (gsBlocks X J j k)ᵀ) =
      if i = j then (∑ k : Fin 4, X k * (X k)ᵀ) else 0 := by
  have hrevT := gs_reverse_transpose X J hJJ hrev
  have hcancel (U : Matrix I I ℤ) : J * (J * U) = U := by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hrevR (a : Fin 4) (U : Matrix I I ℤ) :
      J * (X a * U) = (X a)ᵀ * (J * U) := by
    rw [← Matrix.mul_assoc, hrev a, Matrix.mul_assoc]
  have hrevTR (a : Fin 4) (U : Matrix I I ℤ) :
      J * ((X a)ᵀ * U) = X a * (J * U) := by
    rw [← Matrix.mul_assoc, hrevT a, Matrix.mul_assoc]
  have hcommTT (a b : Fin 4) :
      (X a)ᵀ * (X b)ᵀ = (X b)ᵀ * (X a)ᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose (hcomm b a)
  have hcommR (a b : Fin 4) (U : Matrix I I ℤ) :
      X a * (X b * U) = X b * (X a * U) := by
    rw [← Matrix.mul_assoc, hcomm a b, Matrix.mul_assoc]
  have hmixedR (a b : Fin 4) (U : Matrix I I ℤ) :
      X a * ((X b)ᵀ * U) = (X b)ᵀ * (X a * U) := by
    rw [← Matrix.mul_assoc, hmixed a b, Matrix.mul_assoc]
  have hsucc2 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  fin_cases i <;> fin_cases j <;>
    norm_num [gsBlocks, Fin.sum_univ_succ, hsucc2]
  all_goals
    simp only [Matrix.transpose_mul, Matrix.transpose_neg,
      Matrix.transpose_transpose, hJt, Matrix.mul_assoc,
      hcancel, hrev, hrevT, hrevR, hrevTR, hJJ, Matrix.mul_one, Matrix.one_mul,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg] <;>
    noncomm_ring [hcomm 0 1, hcomm 0 2, hcomm 0 3,
      hcomm 1 2, hcomm 1 3, hcomm 2 3,
      hcommR 0 1, hcommR 0 2, hcommR 0 3,
      hcommR 1 2, hcommR 1 3, hcommR 2 3, hmixed, hmixedR,
      hcommTT 0 1, hcommTT 0 2, hcommTT 0 3,
      hcommTT 1 2, hcommTT 1 3, hcommTT 2 3]

/-- Flattening the block identity gives the row-Gram equation on `Fin 4 × I`. -/
theorem gsMatrix_rowGram
    (X : Fin 4 → Matrix I I ℤ) (J : Matrix I I ℤ) (σ : ℤ)
    (hJt : Jᵀ = J) (hJJ : J * J = 1)
    (hrev : ∀ i, J * X i = (X i)ᵀ * J)
    (hcomm : ∀ i j, X i * X j = X j * X i)
    (hmixed : ∀ i j, X i * (X j)ᵀ = (X j)ᵀ * X i)
    (hgram : (∑ k : Fin 4, X k * (X k)ᵀ) = σ • (1 : Matrix I I ℤ)) :
    gsMatrix X J * (gsMatrix X J)ᵀ =
      σ • (1 : Matrix (Fin 4 × I) (Fin 4 × I) ℤ) := by
  ext p q
  rcases p with ⟨i, r⟩
  rcases q with ⟨j, s⟩
  have hb := congrArg (fun M : Matrix I I ℤ => M r s)
    (gsBlocks_rowGram X J hJt hJJ hrev hcomm hmixed i j)
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
    ] at hb
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gsMatrix,
    Fintype.sum_prod_type]
  rw [hb]
  by_cases hij : i = j
  · subst j
    simp [hgram, Matrix.one_apply, Matrix.intCast_apply]
  · simp [hij]

#print axioms gsBlocks_rowGram
#print axioms gsMatrix_rowGram

end Hadamard892
