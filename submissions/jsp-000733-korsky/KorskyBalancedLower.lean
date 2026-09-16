import KorskyBalancedDefs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/-!
The lower endpoint for balanced ordered ternary words in Korsky's Section 3.
Weights need only be monotone; no positivity or strictness is assumed here.
-/
namespace Erdos882Korsky

lemma balanced_coeff_sum {k : ℕ} {w : Word k} (hw : Balanced w) :
    (∑ i, ((w i : ℤ) - 1)) = 0 := by
  have hs : (∑ i, (w i : ℤ)) = (k : ℤ) := by
    exact_mod_cast hw.2
  rw [Finset.sum_sub_distrib, hs]
  simp

lemma balanced_eq_one_of_no_two {k : ℕ} {w : Word k} (hw : Balanced w)
    (hnot : ∀ i, w i ≠ 2) : ∀ i, w i = 1 := by
  have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin k)), (w i : ℤ) - 1 ≤ 0 := by
    intro i _
    have hi := (w i).isLt
    have hni : (w i).val ≠ 2 := by
      intro h
      exact hnot i (Fin.ext h)
    change (↑(w i).val : ℤ) - 1 ≤ 0
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp (balanced_coeff_sum hw)
  intro i
  apply Fin.ext
  have hi := hz i (Finset.mem_univ i)
  change (↑(w i).val : ℤ) - 1 = 0 at hi
  change (w i).val = 1
  omega

lemma balanced_value_lower {k : ℕ} {a : Fin k → ℕ}
    (ha : Monotone a) {w : Word k} (hw : Balanced w) :
    (total a : ℤ) ≤ value a w := by
  classical
  by_cases ht : ∃ i, w i = 2
  · let T : Finset (Fin k) := Finset.univ.filter (fun i => w i = 2)
    have hT : T.Nonempty := by
      obtain ⟨i, hi⟩ := ht
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let p : Fin k := T.min' hT
    have hpT : p ∈ T := Finset.min'_mem T hT
    have hwp : w p = 2 := (Finset.mem_filter.mp hpT).2
    have hpoint : ∀ i, 0 ≤ ((w i : ℤ) - 1) * ((a i : ℤ) - (a p : ℤ)) := by
      intro i
      by_cases hip : i < p
      · have hwi : (w i : ℤ) - 1 ≤ 0 := by
          have hi := (w i).isLt
          have hni : (w i).val ≠ 2 := by
            intro h
            have him : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, Fin.ext h⟩
            have hpi : p ≤ i := Finset.min'_le T i him
            omega
          change (↑(w i).val : ℤ) - 1 ≤ 0
          omega
        have hai : (a i : ℤ) - (a p : ℤ) ≤ 0 := by
          have h := ha hip.le
          omega
        exact mul_nonneg_of_nonpos_of_nonpos hwi hai
      · have hpi : p ≤ i := le_of_not_gt hip
        have hwi : 0 ≤ (w i : ℤ) - 1 := by
          have hnzero : w i ≠ 0 := by
            rcases eq_or_lt_of_le hpi with h | h
            · simp [← h, hwp]
            · exact hw.1 p i h hwp
          have hval : (w i).val ≠ 0 := by
            intro h
            exact hnzero (Fin.ext h)
          change 0 ≤ (↑(w i).val : ℤ) - 1
          omega
        have hai : 0 ≤ (a i : ℤ) - (a p : ℤ) := by
          have h := ha hpi
          omega
        exact mul_nonneg hwi hai
    have hsum : 0 ≤ ∑ i, ((w i : ℤ) - 1) * ((a i : ℤ) - (a p : ℤ)) :=
      Finset.sum_nonneg (fun i _ => hpoint i)
    have heq : (∑ i, ((w i : ℤ) - 1) * ((a i : ℤ) - (a p : ℤ))) =
        value a w - (total a : ℤ) := by
      calc
        _ = (∑ i, ((w i : ℤ) * (a i : ℤ) - (a i : ℤ) -
            ((w i : ℤ) - 1) * (a p : ℤ))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = value a w - (total a : ℤ) := by
          simp only [Finset.sum_sub_distrib, ← Finset.sum_mul,
            balanced_coeff_sum hw, zero_mul, sub_zero, value, total, Nat.cast_sum]
    rw [heq] at hsum
    omega
  · have hone := balanced_eq_one_of_no_two hw (by simpa only [not_exists] using ht)
    simp [value, total, hone]

end Erdos882Korsky
