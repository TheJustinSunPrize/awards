import KorskyBalancedDefs
import KorskyInject
import Mathlib.Data.Int.Interval

/-! Finite integer-interval packing. The cardinality and interval hypotheses
are proved in the separate balanced-word modules and discharged in the final
module; no new axioms are introduced. -/
namespace Erdos882Korsky

lemma balanced_one (k : ℕ) : Balanced (fun _ : Fin k => (1 : Fin 3)) := by
  constructor
  · intro i j hij hi
    simp at hi
  · simp

lemma value_one {k : ℕ} (a : Fin k → ℕ) :
    value a (fun _ : Fin k => (1 : Fin 3)) = (total a : ℤ) := by
  simp [value, total, Nat.cast_sum]

theorem balanced_interval_packing {k n : ℕ} (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hn : NoDouble a)
    (hc : Fintype.card {w : Word k // Balanced w} = 2^(k-1))
    (hl : ∀ w : Word k, Balanced w → (total a : ℤ) ≤ value a w)
    (hu : ∀ w : Word k, Balanced w →
      value a w + (((k-1)^2/4 : ℕ) : ℤ) ≤ (k*n : ℕ)) :
    total a + 2^(k-1) + (k-1)^2/4 ≤ k*n+1 := by
  classical
  let B := {w : Word k // Balanced w}
  let lo : ℤ := total a
  let hi : ℤ := (k*n : ℕ) - (((k-1)^2/4 : ℕ) : ℤ)
  have hbase : lo ≤ hi := by
    have hb := hu _ (balanced_one k)
    rw [value_one] at hb
    exact (le_sub_iff_add_le).2 hb
  have hcount : Fintype.card B ≤ (Finset.Icc lo hi).card := by
    have h := Finset.card_le_card_of_injOn
      (fun w : B => value a w.val)
      (s := Finset.univ) (t := Finset.Icc lo hi) ?_ ?_
    · simpa using h
    · intro w hw
      apply Finset.mem_Icc.mpr
      constructor
      · exact hl w.val w.property
      · have hh := hu w.val w.property
        exact (le_sub_iff_add_le).2 hh
    · intro u hu v hv heq
      apply Subtype.ext
      exact ordered_value_injective ha hn u.property.1 v.property.1 heq
  have hcountZ : (Fintype.card B : ℤ) ≤ ((Finset.Icc lo hi).card : ℤ) := by
    exact_mod_cast hcount
  have hI : ((Finset.Icc lo hi).card : ℤ) = hi+1-lo :=
    Int.card_Icc_of_le lo hi (by omega : lo ≤ hi+1)
  rw [hI] at hcountZ
  change (Fintype.card {w : Word k // Balanced w} : ℤ) ≤ hi+1-lo at hcountZ
  rw [hc] at hcountZ
  have finish (s p q m : ℕ)
      (h : (p : ℤ) ≤ (m : ℤ) - (q : ℤ) + 1 - (s : ℤ)) :
      s + p + q ≤ m + 1 := by omega
  exact finish (total a) (2^(k-1)) ((k-1)^2/4) (k*n) hcountZ

end Erdos882Korsky
