import KorskyDefs

/-! Balanced ordered words for the finite strengthening in Section 3 of
Samuel Korsky, Near-Exact Bounds for Primitive Subset Sums (2026-07-26).
The direct interval presentation is a rearrangement of the author's argument.
-/
namespace Erdos882Korsky

def Balanced {k : ℕ} (w : Word k) : Prop :=
  Ordered w ∧ (∑ i, (w i).val) = k

noncomputable instance balancedFintype (k : ℕ) :
    Fintype {w : Word k // Balanced w} := Fintype.ofFinite _

end Erdos882Korsky
