import JSP000689.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace JSP000689
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Iterating a one-vertex multiplicative extension bound. -/
theorem growth_iterate (f : Finset V → ℚ) (β : ℚ) (hβ : 0 ≤ β)
    (S T : Finset V) (hTS : T ⊆ S)
    (hstep : ∀ U ⊆ S, ∀ v ∈ U, β * f (U.erase v) ≤ f U) :
    β ^ (S.card - T.card) * f T ≤ f S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases heq : T = S
    · subst T
      simp
    · have hss : T ⊂ S := lt_of_le_of_ne hTS heq
      obtain ⟨v, hvS, hvT⟩ := exists_of_ssubset hss
      have hTe : T ⊆ S.erase v := subset_erase.mpr ⟨hTS, hvT⟩
      have hind := ih (S.erase v) (erase_ssubset hvS) hTe
        (fun U hU w hw => hstep U (hU.trans (erase_subset v S)) w hw)
      have hcard : S.card - T.card = ((S.erase v).card - T.card) + 1 := by
        have hsmall := card_erase_lt_of_mem hvS
        have hc := card_le_card hTe
        have he := card_erase_of_mem hvS
        omega
      rw [hcard, pow_succ]
      calc
        β ^ ((S.erase v).card - T.card) * β * f T =
            β * (β ^ ((S.erase v).card - T.card) * f T) := by ac_rfl
        _ ≤ β * f (S.erase v) := mul_le_mul_of_nonneg_left hind hβ
        _ ≤ f S := hstep S (Subset.refl S) v hvS

/-- Union bound for the failed extensions, expressed as natural-number counts. -/
theorem counting_recurrence (H : Finset (Finset V)) (S : Finset V) (v : V) (hv : v ∈ S) :
    2 * (colors H (S.erase v)).card ≤ (colors H S).card +
      ∑ e ∈ H.filter (fun e => e ⊆ S ∧ v ∈ e), (bad H S v e).card := by
  calc
    2 * (colors H (S.erase v)).card = (extensions H S v).card :=
      (card_extensions H S v hv).symm
    _ ≤ (colors H S ∪ (H.filter fun e => e ⊆ S ∧ v ∈ e).biUnion (bad H S v)).card :=
      card_le_card (extension_cover H S v)
    _ ≤ (colors H S).card + ((H.filter fun e => e ⊆ S ∧ v ∈ e).biUnion (bad H S v)).card :=
      card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left card_biUnion_le _

end JSP000689
