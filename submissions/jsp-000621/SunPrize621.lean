import SunPrize621.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace SunPrize621

theorem sidon_mono {α : Type*} [Add α] {s t : Finset α}
    (hs : Sidon s) (ht : t ⊆ s) : Sidon t := by
  intro a ha b hb c hc d hd h
  exact hs a (ht ha) b (ht hb) c (ht hc) d (ht hd) h

theorem sidon_card_le_eight {s : Finset ℤ} (hsub : s ⊆ base)
    (hs : Sidon s) : s.card ≤ 8 := by
  by_contra h
  have h9 : 9 ≤ s.card := by omega
  obtain ⟨t, hts, ht9⟩ := Finset.exists_subset_card_eq h9
  have htbase : t ⊆ base := hts.trans hsub
  obtain ⟨p, hp, ha, hb, hc⟩ := nine_contains_progression t
    (Finset.mem_powersetCard.mpr ⟨htbase, ht9⟩)
  obtain ⟨hab, _, heq⟩ := progressions_correct p hp
  have hsid := sidon_mono hs hts
  rcases hsid p.1 ha p.2.2 hc p.2.1 hb p.2.1 hb heq with hpair | hpair
  · exact (ne_of_lt hab) hpair.1
  · exact (ne_of_lt hab) hpair.1

noncomputable section
open scoped Classical

def realImage (s : Finset ℤ) : Finset ℝ := s.image (fun n : ℤ => (n : ℝ))

def realBase : Finset ℝ := realImage base

/-- Every four-element subset has at least eleven signed differences. -/
def AlmostSidon (s : Finset ℝ) : Prop :=
  ∀ t : Finset ℝ, t ⊆ s → t.card = 4 → 11 ≤ (differences t).card

/-- The universal guarantee in the original, all-finite-sets formulation. -/
def Admissible (c : ℝ) : Prop :=
  ∀ a : Finset ℝ, AlmostSidon a →
    ∃ s : Finset ℝ, s ⊆ a ∧ Sidon s ∧ c * (a.card : ℝ) ≤ (s.card : ℝ)

theorem realImage_card (s : Finset ℤ) : (realImage s).card = s.card := by
  exact Finset.card_image_of_injective s
    (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℝ)))

theorem differences_realImage (s : Finset ℤ) :
    differences (realImage s) = realImage (differences s) := by
  unfold differences realImage
  rw [← Finset.prodMap_image_product]
  simp only [Finset.image_image]
  apply Finset.image_congr
  rintro ⟨a, b⟩ _
  simp

theorem sidon_realImage_iff (s : Finset ℤ) : Sidon (realImage s) ↔ Sidon s := by
  constructor
  · intro hs a ha b hb c hc d hd heq
    have hcast : (a : ℝ) + (b : ℝ) = (c : ℝ) + (d : ℝ) := by
      exact_mod_cast heq
    have h := hs (a : ℝ) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (b : ℝ) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      (c : ℝ) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
      (d : ℝ) (Finset.mem_image.mpr ⟨d, hd, rfl⟩) hcast
    rcases h with h | h
    · exact Or.inl ⟨Int.cast_injective h.1, Int.cast_injective h.2⟩
    · exact Or.inr ⟨Int.cast_injective h.1, Int.cast_injective h.2⟩
  · intro hs a ha b hb c hc d hd heq
    simp only [realImage, Finset.mem_image] at ha hb hc hd
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    obtain ⟨c, hc, rfl⟩ := hc
    obtain ⟨d, hd, rfl⟩ := hd
    have hint : a + b = c + d := by exact_mod_cast heq
    rcases hs a ha b hb c hc d hd hint with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

theorem realBase_card : realBase.card = 14 := by
  rw [realBase, realImage_card, base_card]

theorem realBase_almostSidon : AlmostSidon realBase := by
  intro t ht ht4
  obtain ⟨s, hs, himage⟩ := Finset.subset_image_iff.mp ht
  change realImage s = t at himage
  subst t
  have hs4 : s.card = 4 := by simpa only [realImage_card] using ht4
  have hcert := base_local_certificate s (Finset.mem_powersetCard.mpr ⟨hs, hs4⟩)
  simpa only [differences_realImage, realImage_card] using hcert

theorem realBase_sidon_bound {s : Finset ℝ} (hsub : s ⊆ realBase)
    (hs : Sidon s) : s.card ≤ 8 := by
  obtain ⟨t, ht, himage⟩ := Finset.subset_image_iff.mp hsub
  change realImage t = s at himage
  subst s
  rw [realImage_card]
  exact sidon_card_le_eight ht ((sidon_realImage_iff t).mp hs)

theorem realBase_has_eight :
    ∃ s : Finset ℝ, s ⊆ realBase ∧ Sidon s ∧ s.card = 8 := by
  refine ⟨realImage witness, ?_, (sidon_realImage_iff witness).mpr witness_sidon, ?_⟩
  · exact Finset.image_subset_image witness_subset
  · rw [realImage_card, witness_card]

/-- Ma--Tang's upper bound for every universal Sidon guarantee. -/
theorem admissible_le_four_sevenths {c : ℝ} (hc : Admissible c) : c ≤ 4 / 7 := by
  obtain ⟨s, hsub, hs, hsize⟩ := hc realBase realBase_almostSidon
  have hbound : (s.card : ℝ) ≤ 8 := by
    exact_mod_cast realBase_sidon_bound hsub hs
  rw [realBase_card] at hsize
  norm_num at hsize
  linarith

end

end SunPrize621
