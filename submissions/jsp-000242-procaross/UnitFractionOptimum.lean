/-
Released under the Apache 2.0 license. Prepared with AI assistance.
-/
import UnitFractionBounds
import Mathlib.Data.Finset.Max

/-!
A total finite optimizer for the smallest denominator. Correctness covers every
cardinality at least three, independently of the sample computations.
-/

namespace UnitFractionBounds

open scoped BigOperators

theorem lower_bound_le_card (A : Finset ℕ) {k m : ℕ} (hk : A.card = k)
    (hm : 0 < m) (hlo : ∀ a ∈ A, m ≤ a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) : m ≤ k := by
  have h := recips_le_uniform A.sort hm
    (fun a ha => hlo a ((Finset.mem_sort (· ≤ ·)).mp ha))
  rw [recips_sort, hsum, Finset.length_sort, hk] at h
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hh := (le_div_iff₀ hmQ).mp h
  exact_mod_cast (by simpa using hh : (m : ℚ) ≤ k)

/-- Splitting a largest denominator preserves the lower bound and adds one term. -/
theorem extend_representation (A : Finset ℕ) {k m : ℕ} (hk : A.card = k)
    (hn : A.Nonempty) (hm : 2 ≤ m) (hlo : ∀ a ∈ A, m ≤ a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    ∃ B : Finset ℕ, B.card = k + 1 ∧ (∀ b ∈ B, m ≤ b) ∧
      (∑ b ∈ B, (1 : ℚ) / b) = 1 := by
  let a := A.max' hn
  have ha : a ∈ A := A.max'_mem hn
  have hmax : ∀ b ∈ A, b ≤ a := fun b hb => A.le_max' b hb
  have hma : m ≤ a := hlo a ha
  have ha2 : 2 ≤ a := hm.trans hma
  have ha0 : 0 < a := by omega
  have hbig : a + 1 < a * (a + 1) := by nlinarith
  have hnew : a + 1 ∉ A := by intro hh; have := hmax _ hh; omega
  have hnew' : a * (a + 1) ∉ A := by intro hh; have := hmax _ hh; omega
  have hnot₁ : a * (a + 1) ∉ A.erase a := by
    intro hh
    exact hnew' (Finset.mem_of_mem_erase hh)
  have hnot₂ : a + 1 ∉ insert (a * (a + 1)) (A.erase a) := by
    simp only [Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨by omega, fun hh => hnew hh.2⟩
  refine ⟨insert (a + 1) (insert (a * (a + 1)) (A.erase a)), ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot₂, Finset.card_insert_of_notMem hnot₁,
      Finset.card_erase_of_mem ha, hk]
    have : 0 < k := by rw [← hk]; exact Finset.card_pos.mpr hn
    omega
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_erase] at hb
    rcases hb with rfl | rfl | ⟨_, hb⟩
    · omega
    · omega
    · exact hlo b hb
  · rw [Finset.sum_insert hnot₂, Finset.sum_insert hnot₁]
    have hsplit : (1 : ℚ) / (a + 1 : ℕ) + 1 / (a * (a + 1) : ℕ) = 1 / a := by
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      push_cast
      field_simp
    have he := Finset.sum_erase_add A (fun b : ℕ => (1 : ℚ) / b) ha
    rw [hsum] at he
    linarith

theorem possible_extend {k m : ℕ} (hm : 2 ≤ m)
    (h : possible k m 1 = true) : possible (k + 1) m 1 = true := by
  have hm0 : 0 < m := by omega
  obtain ⟨A, hk, hlo, hsum⟩ := (possible_iff_finset k m 1 hm0).mp h
  have hn : A.Nonempty := by
    by_contra hnot
    have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    simp [this] at hsum
  obtain ⟨B, hB, hloB, hsumB⟩ := extend_representation A hk hn hm hlo hsum
  exact possible_of_finset B hm0 hB hloB hsumB

/-- Every number of terms at least three has a distinct representation of one. -/
theorem possible_two_of_three_le (k : ℕ) (hk : 3 ≤ k) : possible k 2 1 = true := by
  induction k, hk using Nat.le_induction with
  | base => decide +kernel
  | succ k _ ih => exact possible_extend (by decide) ih

/-- Finite candidate minima; the cardinality bound is proved, not imposed on denominators. -/
def feasibleMinima (k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter fun m => possible k m 1 = true

def optimalMinimum (k : ℕ) : ℕ :=
  if h : (feasibleMinima k).Nonempty then (feasibleMinima k).max' h else 0

theorem feasibleMinima_nonempty (k : ℕ) (hk : 3 ≤ k) : (feasibleMinima k).Nonempty := by
  refine ⟨2, ?_⟩
  simp only [feasibleMinima, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, possible_two_of_three_le k hk⟩

theorem optimalMinimum_mem (k : ℕ) (hk : 3 ≤ k) : optimalMinimum k ∈ feasibleMinima k := by
  rw [optimalMinimum, dite_eq_left (feasibleMinima_nonempty k hk)]
  exact Finset.max'_mem _ _

theorem le_optimalMinimum (k : ℕ) (hk : 3 ≤ k) {m : ℕ}
    (hm : m ∈ feasibleMinima k) : m ≤ optimalMinimum k := by
  rw [optimalMinimum, dite_eq_left (feasibleMinima_nonempty k hk)]
  exact Finset.le_max' _ _ hm

theorem possible_mem_feasible {k m : ℕ} (hm : 0 < m)
    (hp : possible k m 1 = true) : m ∈ feasibleMinima k := by
  obtain ⟨A, hk, hlo, hsum⟩ := (possible_iff_finset k m 1 hm).mp hp
  have hmk := lower_bound_le_card A hk hm hlo hsum
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmk⟩, hp⟩

/-- The finite optimizer decides every positive denominator threshold. -/
theorem possible_iff_le_optimalMinimum (k m : ℕ) (hk : 3 ≤ k) (hm : 0 < m) :
    possible k m 1 = true ↔ m ≤ optimalMinimum k := by
  constructor
  · intro hp
    exact le_optimalMinimum k hk (possible_mem_feasible hm hp)
  · intro hle
    have hb := optimalMinimum_mem k hk
    obtain ⟨hI, hp⟩ := Finset.mem_filter.mp hb
    have hb0 : 0 < optimalMinimum k := (Finset.mem_Icc.mp hI).1
    obtain ⟨A, hA, hlo, hsum⟩ := (possible_iff_finset k (optimalMinimum k) 1 hb0).mp hp
    exact possible_of_finset A hm hA (fun a ha => hle.trans (hlo a ha)) hsum

/-- For every k ≥ 3, the returned number is attained and is globally optimal. -/
theorem optimalMinimum_isGreatest (k : ℕ) (hk : 3 ≤ k) :
    IsGreatest {m | AttainableMinimum k m} (optimalMinimum k) := by
  have hb := optimalMinimum_mem k hk
  obtain ⟨hI, hp⟩ := Finset.mem_filter.mp hb
  have hb0 : 0 < optimalMinimum k := (Finset.mem_Icc.mp hI).1
  obtain ⟨A, hA, hlo, hsum⟩ := (possible_iff_finset k (optimalMinimum k) 1 hb0).mp hp
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => hb0.trans_le (hlo a ha)
  have hmem : optimalMinimum k ∈ A := by
    by_contra hn
    have hlo' : ∀ a ∈ A, optimalMinimum k + 1 ≤ a := by
      intro a ha
      have := hlo a ha
      have : a ≠ optimalMinimum k := by intro he; exact hn (he ▸ ha)
      omega
    have hp' := possible_of_finset A (Nat.succ_pos _) hA hlo' hsum
    have hle := (possible_iff_le_optimalMinimum k (optimalMinimum k + 1) hk (by omega)).mp hp'
    omega
  refine ⟨⟨A, hA, hpos, hsum, hmem, hlo⟩, ?_⟩
  intro m hm
  obtain ⟨B, hB, hposB, hsumB, hmemB, hloB⟩ := hm
  exact (possible_iff_le_optimalMinimum k m hk (hposB m hmemB)).mp
    (possible_of_finset B (hposB m hmemB) hB hloB hsumB)

theorem optimalMinimum_mono_step (k : ℕ) (hk : 3 ≤ k) :
    optimalMinimum k ≤ optimalMinimum (k + 1) := by
  have htwo : 2 ≤ optimalMinimum k :=
    (possible_iff_le_optimalMinimum k 2 hk (by decide)).mp (possible_two_of_three_le k hk)
  have hp : possible k (optimalMinimum k) 1 = true :=
    (possible_iff_le_optimalMinimum k _ hk (by omega)).mpr le_rfl
  exact (possible_iff_le_optimalMinimum (k + 1) _ (by omega) (by omega)).mp
    (possible_extend htwo hp)

theorem optimalMinimum_mono {k l : ℕ} (hk : 3 ≤ k) (hkl : k ≤ l) :
    optimalMinimum k ≤ optimalMinimum l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact ih.trans (optimalMinimum_mono_step l (hk.trans hl))

/-- Zero denotes infeasibility only in the exceptional cardinalities zero and two. -/
theorem exceptional_cardinalities :
    optimalMinimum 0 = 0 ∧ optimalMinimum 1 = 1 ∧ optimalMinimum 2 = 0 := by
  decide +kernel

end UnitFractionBounds

#print axioms UnitFractionBounds.extend_representation
#print axioms UnitFractionBounds.possible_two_of_three_le
#print axioms UnitFractionBounds.possible_iff_le_optimalMinimum
#print axioms UnitFractionBounds.optimalMinimum_isGreatest
#print axioms UnitFractionBounds.optimalMinimum_mono_step
#print axioms UnitFractionBounds.optimalMinimum_mono
#print axioms UnitFractionBounds.exceptional_cardinalities
