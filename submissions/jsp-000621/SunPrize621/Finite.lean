import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-!
# The Ma--Tang fourteen-point witness for Erdős 757 / JSP-000621

Mathematical construction: Jie Ma and Quanyu Tang, arXiv:2602.23282v1,
Lemma 5.1. The intended contribution is formalization, not discovery.
The optimal constant remains open; this development concerns its upper bound.
-/

namespace SunPrize621

/-- All unordered pair sums, including repeated summands, are unique. -/
def Sidon {α : Type*} [Add α] (s : Finset α) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Signed differences, including zero, as a finite set. -/
def differences {α : Type*} [Sub α] [DecidableEq α] (s : Finset α) : Finset α :=
  (s ×ˢ s).image (fun p => p.1 - p.2)

def base : Finset ℤ :=
  {0, 136, 200, 243, 246, 249, 272, 286, 298, 323, 400, 528, 596, 1056}

def witness : Finset ℤ := {0, 136, 200, 243, 246, 298, 323, 528}

/-- Explicit arithmetic progressions in the base set. -/
def progressions : Finset (ℤ × ℤ × ℤ) :=
  {(0, 136, 272), (0, 200, 400), (0, 298, 596), (0, 528, 1056),
   (136, 596, 1056), (200, 243, 286), (200, 249, 298),
   (243, 246, 249), (246, 272, 298), (246, 323, 400),
   (249, 286, 323), (272, 400, 528)}

theorem base_card : base.card = 14 := by decide +kernel

theorem witness_subset : witness ⊆ base := by decide +kernel

theorem witness_card : witness.card = 8 := by decide +kernel

theorem witness_sidon : Sidon witness := by
  unfold Sidon witness
  decide +kernel

theorem progressions_correct :
    ∀ t ∈ progressions, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      t.1 + t.2.2 = t.2.1 + t.2.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_local_certificate :
    ∀ s ∈ base.powersetCard 4, 11 ≤ (differences s).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nine_contains_progression :
    ∀ s ∈ base.powersetCard 9,
      ∃ t ∈ progressions, t.1 ∈ s ∧ t.2.1 ∈ s ∧ t.2.2 ∈ s := by
  decide +kernel

end SunPrize621
