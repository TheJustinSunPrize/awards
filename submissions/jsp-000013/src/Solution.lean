/-
Licensed under Apache-2.0; see LICENSE and NOTICE.
Adapted from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz,
Arthur742Ramos/hadamard-668-lean at 78fbae8d69b6fdb66705b662469692d60e346ef0.
Modification: certify the distinct order-716 matrix with fresh certificate data.
Matrix discovery belongs to the original Alpoge/Voinov/Reynolds-Haertle team.
-/
import Hadamard716.MatrixProof

open scoped BigOperators

namespace Hadamard716

def IsHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, H i j = -1 ∨ H i j = 1) ∧
  (∀ i, ∑ j, H i j * H i j = n) ∧
  (∀ i k, i ≠ k → ∑ j, H i j * H k j = 0)

theorem hadamard_716_exists :
    ∃ H : Matrix (Fin 716) (Fin 716) ℤ, IsHadamard H := by
  refine ⟨matrix716, ?_⟩
  unfold IsHadamard
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact matrix716_entry_sign i j
  · intro i
    exact matrix716_row_norm i
  · intro i k hne
    exact matrix716_row_orthogonal hne

end Hadamard716

#print axioms Hadamard716.hadamard_716_exists
