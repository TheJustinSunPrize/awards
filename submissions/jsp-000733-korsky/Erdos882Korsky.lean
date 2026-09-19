import KorskyCount
import KorskyInject
import KorskyModular
import KorskyEndpoint

/-!
# Korsky's sum bound and constant-error upper bound for Erdős 882
Mathematical source: Samuel Korsky, Near-Exact Bounds for Primitive Subset Sums,
July 26, 2026. This is a new Lean formalization, not a new mathematical result.
The proof uses an equivalent finite modular form of the ordered ternary packing.
This package does not import or reproduce the existing ELRSS lower proof.
-/
namespace Erdos882Korsky

/-- Korsky's sum bound under the weaker hypothesis excluding only ratio two. -/
theorem korsky_sum_bound {k : ℕ} (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hn : NoDouble a) :
    k * 2 ^ (k - 1) ≤ total a := by
  rw [← good_card k hk]
  apply good_card_le_total hk a ha
  · intro u v hu hv h
    exact ordered_value_injective ha hn hu.1 hv.1 h
  · intro u v hu hv
    exact good_value_ne_add_total ha hn hu hv

/-- Upper bound for the actual attained maximum of the original problem. -/
theorem original_upper_bound (n : ℕ) :
    Erdos882.maximumSize n ≤ Nat.log 2 n + 1 :=
  maximumSize_le_log_add_one korsky_sum_bound n

end Erdos882Korsky

#print axioms Erdos882Korsky.korsky_sum_bound
#print axioms Erdos882Korsky.original_upper_bound
