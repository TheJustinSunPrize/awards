/-
Order-716 bridge to Mathlib's standard Hadamard predicate.
See NOTICE for the underlying matrix and reused certificate-proof attribution.
Released under Apache-2.0.
-/
import Solution
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

open scoped BigOperators
namespace Hadamard716

private theorem isHadamard_of_rows
    (H : Matrix (Fin 716) (Fin 716) ℤ)
    (hs : ∀ i j, H i j = -1 ∨ H i j = 1)
    (hn : ∀ i, ∑ j, H i j * H i j = 716)
    (ho : ∀ {i j}, i ≠ j → ∑ k, H i k * H j k = 0) :
    Matrix.IsHadamard H := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    rcases hs i j with h | h <;> simp [h, Unitary.mem_iff]
  · ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hn i
    · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hij]
        using ho hij
  · norm_num [isRegular_iff_ne_zero]

theorem matrix716_isHadamard : Matrix.IsHadamard matrix716 :=
  isHadamard_of_rows matrix716 matrix716_entry_sign matrix716_row_norm
    (fun {_ _} h => matrix716_row_orthogonal h)

theorem hadamard_716_exists_standard :
    ∃ H : Matrix (Fin 716) (Fin 716) ℤ, Matrix.IsHadamard H :=
  ⟨matrix716, matrix716_isHadamard⟩

end Hadamard716
#print axioms Hadamard716.hadamard_716_exists_standard
