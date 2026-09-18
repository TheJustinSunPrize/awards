import JSP000853.Deletion
import JSP000853.ExtensionCounting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite colouring counts for the lower bound

We model Bernoulli sampling without measure theory: choose a uniformly counted
colouring and keep the zero colour class.  The lemmas below compute the exact
number of colourings satisfying one or three prescribed zero constraints.
-/

namespace JSP000853

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Finite averaging in a subtraction-free form.  If the sum of the scaled
good counts dominates the scaled bad counts plus a fixed gain for every
sample, then some individual sample realizes that gain. -/
theorem exists_scaled_bad_add_le_good {ι : Type*} [Fintype ι] [Nonempty ι]
    (good bad : ι → ℕ) (scale gain : ℕ)
    (hsum : scale * (∑ i, bad i) + Fintype.card ι * gain ≤
      scale * (∑ i, good i)) :
    ∃ i, scale * bad i + gain ≤ scale * good i := by
  by_contra h
  have hall : ∀ i, scale * good i < scale * bad i + gain := by
    intro i
    exact Nat.lt_of_not_ge (not_exists.mp h i)
  have hstrict : (∑ i, scale * good i) < ∑ i, (scale * bad i + gain) := by
    apply Finset.sum_lt_sum (fun i _hi ↦ (hall i).le)
    let i : ι := Classical.choice inferInstance
    exact ⟨i, Finset.mem_univ i, hall i⟩
  have hcontr : scale * (∑ i, good i) <
      scale * (∑ i, bad i) + Fintype.card ι * gain := by
    calc
      scale * (∑ i, good i) = ∑ i, scale * good i := by
        rw [Finset.mul_sum]
      _ < ∑ i, (scale * bad i + gain) := hstrict
      _ = scale * (∑ i, bad i) + Fintype.card ι * gain := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Nat.nsmul_eq_mul, Finset.card_univ]
  exact (Nat.not_lt_of_ge hsum) hcontr

theorem card_colorings_eq_at (x : α) (z : β) :
    ((Finset.univ : Finset (α → β)).filter fun c ↦ c x = z).card =
      Fintype.card β ^ (Fintype.card α - 1) := by
  classical
  simpa using card_filter_function_extensions ({x} : Finset α) (fun _ ↦ z)

theorem card_colorings_eq_at_three {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (b : β) :
    ((Finset.univ : Finset (α → β)).filter fun c ↦
      c x = b ∧ c y = b ∧ c z = b).card =
        Fintype.card β ^ (Fintype.card α - 3) := by
  classical
  have hcard : ({x, y, z} : Finset α).card = 3 := by
    simp [hxy, hxz, hyz]
  have h := card_filter_function_extensions ({x, y, z} : Finset α) (fun _ ↦ b)
  rw [hcard] at h
  simpa [hxy, hxz, hyz] using h

/-- The colour class selected by a distinguished colour. -/
def colorClass (b : β) (c : α → β) : Finset α :=
  Finset.univ.filter fun x ↦ c x = b

theorem sum_card_colorClass (b : β) :
    ∑ c : α → β, (colorClass b c).card =
      Fintype.card α * Fintype.card β ^ (Fintype.card α - 1) := by
  classical
  calc
    ∑ c : α → β, (colorClass b c).card =
        ∑ c : α → β, ∑ x : α, if c x = b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      unfold colorClass
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x : α, ∑ c : α → β, if c x = b then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _x : α, Fintype.card β ^ (Fintype.card α - 1) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← card_colorings_eq_at x b]
      conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = Fintype.card α * Fintype.card β ^ (Fintype.card α - 1) := by
      simpa only [Finset.card_univ] using
        (Finset.sum_const_nat (s := (Finset.univ : Finset α))
          (m := Fintype.card β ^ (Fintype.card α - 1)) (fun _ _ ↦ rfl))

namespace PairMapping

variable (f : PairMapping α)

omit [Fintype α] in
theorem map_triple_card {x y : α} (hxy : x ≠ y) :
    ({x, y, f x y} : Finset α).card = 3 := by
  have hx : x ∉ ({y, f x y} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, fun h ↦ f.map_ne_left hxy h.symm⟩
  have hy : y ∉ ({f x y} : Finset α) := by
    simpa only [Finset.mem_singleton] using fun h ↦ f.map_ne_right hxy h.symm
  rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy]
  rfl

omit [Fintype β] in
theorem badPairs_colorClass_eq_filter (b : β) (c : α → β) :
    f.badPairs (colorClass b c) =
      (Finset.univ : Finset α).offDiag.filter fun p ↦
        c p.1 = b ∧ c p.2 = b ∧ c (f p.1 p.2) = b := by
  ext p
  simp only [badPairs, Finset.mem_filter, Finset.mem_offDiag, colorClass,
    Finset.mem_univ, Finset.mem_filter, true_and]
  aesop

theorem sum_card_badPairs_colorClass (b : β) :
    ∑ c : α → β, (f.badPairs (colorClass b c)).card =
      (Fintype.card α * (Fintype.card α - 1)) *
        Fintype.card β ^ (Fintype.card α - 3) := by
  classical
  let P : Finset (α × α) := (Finset.univ : Finset α).offDiag
  calc
    ∑ c : α → β, (f.badPairs (colorClass b c)).card =
        ∑ c : α → β, ∑ p ∈ P,
          if c p.1 = b ∧ c p.2 = b ∧ c (f p.1 p.2) = b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [badPairs_colorClass_eq_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ c : α → β,
          if c p.1 = b ∧ c p.2 = b ∧ c (f p.1 p.2) = b then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _p ∈ P, Fintype.card β ^ (Fintype.card α - 3) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hxy : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
      rw [← card_colorings_eq_at_three hxy
        (f.map_ne_left hxy).symm (f.map_ne_right hxy).symm b]
      conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (Fintype.card α * (Fintype.card α - 1)) *
          Fintype.card β ^ (Fintype.card α - 3) := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.offDiag_card,
        Finset.card_univ, ← Nat.mul_sub_one]

end PairMapping

end JSP000853
