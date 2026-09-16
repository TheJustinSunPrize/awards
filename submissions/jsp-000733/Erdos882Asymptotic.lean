import Erdos882Upper
import AsymptoticCore

/-!
# Leading asymptotic for primitive subset sums (JSP-000733 / Erdős 882)

The lower bound is the attributed existing ELRSS construction in
Erdos882Existing. The new finite upper bridge is in Erdos882Upper.
Their assembly proves that the actual finite extremal maximum is
asymptotic to log base two of n. No exact formula or constant-error
refinement is asserted.
-/

open Filter
open scoped Topology

namespace Erdos882

/-- The maximum size of A ⊆ {1,…,n} whose distinct nonempty subset-sum
values never divide one another has leading asymptotic log₂ n. -/
theorem maximumSize_asymptotic :
    Tendsto (fun n : ℕ => (maximumSize n : ℝ) / Real.logb 2 (n : ℝ))
      atTop (𝓝 1) :=
  PrimitiveSubsetSums.asymptotic_of_counting_bounds maximumSize
    (fun n _ => maximumSize_pow_le n) erdos_882

end Erdos882

#print axioms Erdos882.maximumSize_asymptotic
#print axioms Erdos882.maximumSize_pow_le
#print axioms Erdos882.erdos_882
