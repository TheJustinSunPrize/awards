import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-! Deterministic counting lemma for Erdős 1166 / JSP-000971.
Time n includes visits at 0,...,n. No probabilistic input is assumed.
-/
namespace JSP000971
open Finset
variable {α : Type*} [DecidableEq α]

def visits (s : ℕ → α) (n : ℕ) (x : α) : ℕ :=
  ((range (n + 1)).filter (fun k => s k = x)).card

def visited (s : ℕ → α) (n : ℕ) : Finset α := (range (n + 1)).image s

def maximum (s : ℕ → α) (n : ℕ) : ℕ :=
  (visited s n).sup (visits s n)

def favorites (s : ℕ → α) (n : ℕ) : Finset α :=
  (visited s n).filter (fun x => visits s n x = maximum s n)

def historical (s : ℕ → α) (n : ℕ) : Finset α :=
  (range (n + 1)).biUnion (favorites s)

lemma visited_mono (s : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    visited s a ⊆ visited s b := by
  apply image_subset_image
  exact range_mono (by omega)

lemma visits_mono (s : ℕ → α) (x : α) {a b : ℕ} (h : a ≤ b) :
    visits s a x ≤ visits s b x := by
  apply card_le_card
  exact filter_subset_filter _ (range_mono (by omega))

lemma visits_le_maximum (s : ℕ → α) {n : ℕ} {x : α}
    (hx : x ∈ visited s n) : visits s n x ≤ maximum s n :=
  Finset.le_sup hx

lemma maximum_mono (s : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    maximum s a ≤ maximum s b := by
  apply Finset.sup_le
  intro x hx
  exact (visits_mono s x h).trans (visits_le_maximum s (visited_mono s h hx))

lemma maximum_pos (s : ℕ → α) (n : ℕ) : 1 ≤ maximum s n := by
  have hx : s 0 ∈ visited s n := mem_image.mpr ⟨0, by simp, rfl⟩
  have hv : 0 < visits s n (s 0) := by
    apply card_pos.mpr
    exact ⟨0, by simp⟩
  exact (by omega : 1 ≤ visits s n (s 0)).trans (visits_le_maximum s hx)

lemma visits_pos_iff (s : ℕ → α) (n : ℕ) (x : α) :
    0 < visits s n x ↔ x ∈ visited s n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := card_pos.mp h
    obtain ⟨hkr, hkx⟩ := mem_filter.mp hk
    exact mem_image.mpr ⟨k, hkr, hkx⟩
  · intro h
    obtain ⟨k, hk, hkx⟩ := mem_image.mp h
    exact card_pos.mpr ⟨k, mem_filter.mpr ⟨hk, hkx⟩⟩

/-- Fidelity check: favorites are precisely ALL maximizers among all sites,
not an arbitrarily selected winner or a subset of tied winners. -/
lemma mem_favorites_iff (s : ℕ → α) (n : ℕ) (x : α) :
    x ∈ favorites s n ↔ ∀ y, visits s n y ≤ visits s n x := by
  constructor
  · intro hx y
    obtain ⟨_, heq⟩ := mem_filter.mp hx
    rw [heq]
    by_cases hy : y ∈ visited s n
    · exact visits_le_maximum s hy
    · have hz : visits s n y = 0 := by
        have := (visits_pos_iff s n y).not.mpr hy
        omega
      omega
  · intro hx
    have hzero : s 0 ∈ visited s n := mem_image.mpr ⟨0, by simp, rfl⟩
    have hpos := (visits_pos_iff s n (s 0)).mpr hzero
    have hxpos : 0 < visits s n x := lt_of_lt_of_le hpos (hx (s 0))
    have hxv := (visits_pos_iff s n x).mp hxpos
    apply mem_filter.mpr
    refine ⟨hxv, Nat.le_antisymm (visits_le_maximum s hxv) ?_⟩
    exact Finset.sup_le (fun y _ => hx y)

lemma favorites_persist (s : ℕ → α) {a b : ℕ} (hab : a ≤ b)
    (hm : maximum s a = maximum s b) : favorites s a ⊆ favorites s b := by
  intro x hx
  obtain ⟨hxv, hxe⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨visited_mono s hab hxv, ?_⟩
  apply Nat.le_antisymm (visits_le_maximum s (visited_mono s hab hxv))
  rw [← hm, ← hxe]
  exact visits_mono s x hab

/-- General grouping lemma: within each integer level, earlier sets persist
in later sets. Charge their union to the last time at that level. -/
lemma grouped_union_bound (F : ℕ → Finset α) (M : ℕ → ℕ)
    (N n K : ℕ)
    (hpos : ∀ k ∈ Icc N n, 1 ≤ M k)
    (hmax : ∀ k ∈ Icc N n, M k ≤ M n)
    (hpersist : ∀ a ∈ Icc N n, ∀ b ∈ Icc N n,
      a ≤ b → M a = M b → F a ⊆ F b)
    (hcard : ∀ k ∈ Icc N n, (F k).card ≤ K) :
    ((Icc N n).biUnion F).card ≤ K * M n := by
  let levels := (Icc N n).image M
  let fiber := fun m => (Icc N n).filter (fun k => M k = m)
  let last := fun m => (fiber m).sup id
  have hlast : ∀ m ∈ levels, last m ∈ fiber m := by
    intro m hm
    obtain ⟨k, hk, hkm⟩ := mem_image.mp hm
    have hn : (fiber m).Nonempty := ⟨k, mem_filter.mpr ⟨hk, hkm⟩⟩
    have hs := Finset.sup_mem_of_nonempty (f := id) hn
    simpa only [Set.image_id, Finset.mem_coe] using hs
  have hcover : (Icc N n).biUnion F ⊆ levels.biUnion (fun m => F (last m)) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
    have hmk : M k ∈ levels := mem_image.mpr ⟨k, hk, rfl⟩
    have hl := mem_filter.mp (hlast (M k) hmk)
    apply mem_biUnion.mpr
    refine ⟨M k, hmk, ?_⟩
    apply hpersist k hk (last (M k)) hl.1 ?_ hl.2.symm hx
    exact Finset.le_sup (f := id) (mem_filter.mpr ⟨hk, rfl⟩)
  have hlevel : levels ⊆ Icc 1 (M n) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr ⟨hpos k hk, hmax k hk⟩
  have hcount : levels.card ≤ M n := by
    simpa using card_le_card hlevel
  calc
    ((Icc N n).biUnion F).card ≤ (levels.biUnion (fun m => F (last m))).card :=
      card_le_card hcover
    _ ≤ levels.card * K := card_biUnion_le_card_mul _ _ _ (by
      intro m hm
      exact hcard _ (mem_filter.mp (hlast m hm)).1)
    _ ≤ M n * K := Nat.mul_le_mul_right K hcount
    _ = K * M n := Nat.mul_comm _ _

/-- The independent pathwise counting theorem. The hypothesis is needed only
on [N,n]. The conclusion counts distinct sites, including all ties. -/
theorem historical_card_le (s : ℕ → α) (N n K : ℕ)
    (hK : ∀ k, N ≤ k → k ≤ n → (favorites s k).card ≤ K) :
    (historical s n).card ≤ N + K * maximum s n := by
  have hlate : ((Icc N n).biUnion (favorites s)).card ≤ K * maximum s n := by
    apply grouped_union_bound (favorites s) (maximum s) N n K
    · intro k _; exact maximum_pos s k
    · intro k hk; exact maximum_mono s (mem_Icc.mp hk).2
    · intro a _ b _ hab hm; exact favorites_persist s hab hm
    · intro k hk; exact hK k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
  have hcover : historical s n ⊆
      (range N).image s ∪ (Icc N n).biUnion (favorites s) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := mem_biUnion.mp hx
    by_cases hearly : k < N
    · apply mem_union_left
      obtain ⟨j, hj, rfl⟩ := mem_image.mp (mem_filter.mp hx).1
      apply mem_image.mpr
      exact ⟨j, mem_range.mpr (by have := mem_range.mp hj; omega), rfl⟩
    · apply mem_union_right
      exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨by omega, by
        have := mem_range.mp hk; omega⟩, hx⟩
  calc
    (historical s n).card ≤ ((range N).image s ∪ (Icc N n).biUnion (favorites s)).card :=
      card_le_card hcover
    _ ≤ ((range N).image s).card + ((Icc N n).biUnion (favorites s)).card := card_union_le _ _
    _ ≤ N + K * maximum s n := Nat.add_le_add (by
      simpa using card_image_le (s := range N) (f := s)) hlate

#print axioms historical_card_le
#print axioms grouped_union_bound
end JSP000971
