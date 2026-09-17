import PerfectDifference
import Mathlib.Data.Finset.Sort
open Finset PerfectDifference

-- Small concrete proof terms are reduced by the kernel, not native evaluation.
example : differences {1,2,4,8} = {0,1,2,3,4,6,7} := by decide +kernel
example : 5 ∉ differences {1,2,4,8} := by decide +kernel
example : Sidon {1,2,4,8} := by unfold Sidon; decide +kernel
example : ¬ Sidon {1,2,3} := by unfold Sidon; decide +kernel
example : Perfect (completion {1,2,4,8}) :=
  completion_perfect (by unfold Sidon; decide +kernel) (by decide +kernel)

-- Executable outputs are cross-checked by Python, separately from proof checking.
#eval (List.range 7).map (fun n => (stage ∅ n).sort (· ≤ ·))
#eval (List.range 7).map (fun n => nextDiff (stage ∅ n))
#eval (List.range 6).map (fun n => (stage {1,2,4,8} n).sort (· ≤ ·))
#eval (List.range 6).map (fun n => nextDiff (stage {1,2,4,8} n))
