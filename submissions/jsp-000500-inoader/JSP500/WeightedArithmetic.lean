import Std

/-!
Arithmetic endpoints for a counting proof of the weighted light-edge lemma.
These are unconditional arithmetic results. The graph-theoretic bridge is
implemented separately; these endpoints alone do not prove the prize target.
-/

namespace JSP500.WeightedArithmetic

theorem budget_eight_impossible (m z h l : Nat)
    (hm : 6 ≤ m) (hb : m + z ≤ 8) (hh : 2 ≤ h)
    (hs : 4 * h + 3 * l ≤ 2 * m + z)
    (he : m ≤ h * (h - 1) / 2 + h * l) : False := by
  have hc : h = 2 ∨ h = 3 ∨ h = 4 := by omega
  rcases hc with rfl | rfl | rfl <;> simp at he <;> omega

theorem budget_nine_impossible (m z k : Nat)
    (hm : 6 ≤ m) (hb : m + z ≤ 9)
    (hs : 4 * k ≤ 2 * m + z)
    (he : m ≤ k * (k - 1) / 2) : False := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp at he <;> omega

theorem high_weighted_degree (m z d w du dv zu zv bound : Nat)
    (hb : m + z ≤ bound + 2) (hv : 5 ≤ d + w)
    (hdegrees : du + dv + d ≤ m + 3)
    (hweights : zu + zv + w ≤ z) :
    du + dv + zu + zv ≤ bound := by omega

end JSP500.WeightedArithmetic
