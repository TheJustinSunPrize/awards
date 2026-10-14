import GenericGS
import CirculantBridge
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Hadamard892
open scoped Matrix

lemma neg_signs {z : ℤ} (h : z = 1 ∨ z = -1) : -z = 1 ∨ -z = -1 := by
  rcases h with h | h <;> simp [h]

section
variable {I : Type*} [Fintype I] [DecidableEq I] [AddCommGroup I]

lemma gs_circulant_signs (a : Fin 4 → I → ℤ)
    (ha : ∀ i x, a i x = 1 ∨ a i x = -1) (p q : Fin 4 × I) :
    gsMatrix (fun i => Matrix.circulant (a i)) (reflection I) p q = 1 ∨
    gsMatrix (fun i => Matrix.circulant (a i)) (reflection I) p q = -1 := by
  rcases p with ⟨i, r⟩
  rcases q with ⟨j, s⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact circulant_entry_signs _ (ha _) r s
    | exact circulant_reflection_entry_signs _ (ha _) r s
    | exact transpose_circulant_reflection_entry_signs _ (ha _) r s
    | exact neg_signs (circulant_reflection_entry_signs _ (ha _) r s)
    | exact neg_signs (transpose_circulant_reflection_entry_signs _ (ha _) r s)

/-- Classical Goethals--Seidel construction, with all matrix hypotheses discharged
from signs and periodic autocorrelations of four input sequences. -/
theorem goethals_seidel_hadamard (a : Fin 4 → I → ℤ)
    (ha : ∀ i x, a i x = 1 ∨ a i x = -1)
    (hc : ∀ t : I, (∑ i, corr (a i) t) =
      if t = 0 then (4 * Fintype.card I : ℤ) else 0)
    (hI : Fintype.card I ≠ 0) :
    (gsMatrix (fun i => Matrix.circulant (a i)) (reflection I)).IsHadamard := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro p q
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (gs_circulant_signs a ha p q)
  · have hg := gsMatrix_rowGram (fun i => Matrix.circulant (a i))
      (reflection I) (4 * Fintype.card I)
      reflection_transpose reflection_mul_self
      (fun i => reflection_mul_circulant (a i))
      (fun i j => circulant_commute (a i) (a j))
      (fun i j => circulant_transpose_commute (a i) (a j))
      (correlations_sum_gram a (4 * Fintype.card I) hc)
    simpa [Fintype.card_prod] using hg
  · rw [isRegular_iff_ne_zero]
    simp [Fintype.card_prod, hI]
end

#print axioms gs_circulant_signs
#print axioms goethals_seidel_hadamard
end Hadamard892
