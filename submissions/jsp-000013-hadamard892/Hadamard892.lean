import GenericHadamard
import Hadamard892Certificate
import Mathlib.Logic.Equiv.Fin.Basic

/-!
A fully specified Hadamard matrix of order 892, built from publicly recorded
sign data using the classical Goethals--Seidel construction.
This finite-order theorem does not settle the general Hadamard conjecture.
-/
namespace Hadamard892
set_option maxRecDepth 200000
open scoped Matrix

/-- The concrete matrix, indexed by `Fin 892`. -/
def matrix892 : Matrix (Fin 892) (Fin 892) ℤ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (gsMatrix (fun i => Matrix.circulant (seed i)) (reflection (Fin 223)))

/-- The concrete matrix satisfies Mathlib's complete standard Hadamard predicate. -/
theorem matrix892_isHadamard : matrix892.IsHadamard := by
  apply Matrix.IsHadamard.reindex finProdFinEquiv finProdFinEquiv
  apply goethals_seidel_hadamard seed seed_signs
  · intro t
    change (∑ i : Fin 4, corr (seed i) t) = if t = 0 then (892 : ℤ) else 0
    exact seed_correlations t
  · decide

/-- Unconditional existence at the finite order 892. -/
theorem exists_hadamard892 :
    ∃ H : Matrix (Fin 892) (Fin 892) ℤ, Matrix.IsHadamard H :=
  ⟨matrix892, matrix892_isHadamard⟩

#print axioms goethals_seidel_hadamard
#print axioms matrix892_isHadamard
#print axioms exists_hadamard892
end Hadamard892
