import Erdos882Korsky
import KorskyBalancedCount
import KorskyBalancedLower
import KorskyBalancedUpper
import KorskyBalancedPacking
import KorskyFiniteEndpoint

/-!
# Korsky's strengthened finite upper bound for primitive subset sums

Mathematical source: Samuel Korsky, Near-Exact Bounds for Primitive Subset Sums,
2026-07-26, Theorem 1.1 (1.7)-(1.8) and Section 3. This extends the earlier
sum-bound formalization with balanced-word packing into a finite interval.
Mathematical discovery is attributed to the author, not this formalization.
The independent original-problem definition is unchanged. No lower-bound
construction or exact-value theorem is asserted in this module.
-/
namespace Erdos882Korsky

/-- The deficit estimate, expressed without truncated subtraction. -/
theorem korsky_deficit_bound {k n : ℕ} (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hstrict : StrictMono a) (hn : NoDouble a)
    (hmax : ∀ i, a i ≤ n) :
    total a + 2^(k-1) + (k-1)^2/4 ≤ k*n+1 := by
  apply balanced_interval_packing a ha hn (balanced_card k hk)
  · intro w hw
    exact balanced_value_lower hstrict.monotone hw
  · intro w hw
    exact balanced_value_upper hstrict hmax hw

/-- Korsky's full finite bound. The hypotheses concern the actual distinct
positive generators, with no unproved packing or counting assumptions. -/
theorem korsky_finite_bound {k n : ℕ} (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hstrict : StrictMono a) (hn : NoDouble a)
    (hmax : ∀ i, a i ≤ n) :
    (k+1)*2^(k-1) + (k-1)^2/4 ≤ k*n+1 := by
  have hs := korsky_sum_bound hk a ha hn
  have hd := korsky_deficit_bound hk a ha hstrict hn hmax
  nlinarith

/-- The strengthened bound for any nonempty admissible set in the original
Erdős problem, using the standard finite subset-sum/divisibility condition. -/
theorem original_finite_bound {n : ℕ} {A : Finset ℕ}
    (hA : Erdos882.Admissible n A) (hk : 0 < A.card) :
    (A.card+1)*2^(A.card-1) + (A.card-1)^2/4 ≤ A.card*n+1 :=
  admissible_finite_bound_of_bound korsky_finite_bound hA hk

/-- An explicit finite threshold for the attained maximum. This does not
assert equality without the separate classical lower-bound construction. -/
theorem original_threshold_bound (n m : ℕ)
    (hthreshold : (m+1)*n+1 < (m+2)*2^m + m^2/4) :
    Erdos882.maximumSize n ≤ m :=
  maximumSize_le_of_finite_threshold korsky_finite_bound n m hthreshold

end Erdos882Korsky

#print axioms Erdos882Korsky.korsky_deficit_bound
#print axioms Erdos882Korsky.korsky_finite_bound
#print axioms Erdos882Korsky.original_finite_bound
#print axioms Erdos882Korsky.original_threshold_bound
