/-
Order-716 bridge to Mathlib's standard Hadamard predicate.
See NOTICE for the underlying matrix and reused certificate-proof attribution.
Released under Apache-2.0.
-/
import Solution
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

open scoped BigOperators
namespace Hadamard716

theorem matrix716_isHadamard : Matrix.IsHadamard matrix716 := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    rcases matrix716_entry_sign i j with h | h <;> simp [h, Unitary.mem_iff]
  · ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using matrix716_row_norm i
    · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hij]
        using matrix716_row_orthogonal hij
  · norm_num [isRegular_iff_ne_zero]

theorem hadamard_716_exists_standard :
    ∃ H : Matrix (Fin 716) (Fin 716) ℤ, Matrix.IsHadamard H :=
  ⟨matrix716, matrix716_isHadamard⟩

end Hadamard716
#print axioms Hadamard716.hadamard_716_exists_standard
