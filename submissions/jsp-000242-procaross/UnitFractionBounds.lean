/-
Released under the Apache 2.0 license. Prepared with AI assistance.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Certified finite bounds for distinct Egyptian fractions

This development concerns finite cases of JSP-000242. It does not claim the
asymptotic theorem of Croot, new mathematics, or first-formalization priority.
The search bound is derived from the remaining reciprocal sum. There is no
arbitrary bound on the largest denominator.
-/

namespace UnitFractionBounds

open scoped BigOperators

def recips (l : List ℕ) : ℚ := (l.map fun a : ℕ => (1 : ℚ) / (a : ℚ)).sum

@[simp] theorem recips_nil : recips [] = 0 := rfl

@[simp] theorem recips_cons (a : ℕ) (l : List ℕ) :
    recips (a :: l) = 1 / (a : ℚ) + recips l := rfl

def envelope : ℕ → ℕ → ℚ
  | 0, _ => 0
  | k + 1, m => 1 / (m : ℚ) + envelope k (m + 1)

theorem recips_nonneg (l : List ℕ) : 0 ≤ recips l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    exact add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg a)) ih

theorem recips_le_uniform (l : List ℕ) {m : ℕ} (hm : 0 < m)
    (hlo : ∀ a ∈ l, m ≤ a) : recips l ≤ (l.length : ℚ) / m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : m ≤ a := hlo a (by simp)
    have ht : ∀ b ∈ l, m ≤ b := fun b hb => hlo b (by simp [hb])
    have hr : (1 : ℚ) / a ≤ 1 / m :=
      one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast ha)
    have hi := ih ht
    simp only [recips_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      1 / (a : ℚ) + recips l ≤ 1 / m + (l.length : ℚ) / m := add_le_add hr hi
      _ = ((l.length : ℚ) + 1) / m := by ring

/-- Distinct increasing denominators are bounded term by term by consecutive ones. -/
theorem recips_le_envelope (l : List ℕ) {m : ℕ} (hm : 0 < m)
    (hs : l.Pairwise (· < ·)) (hlo : ∀ a ∈ l, m ≤ a) :
    recips l ≤ envelope l.length m := by
  induction l generalizing m with
  | nil => simp [envelope]
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have ha : m ≤ a := hlo a (by simp)
    have ht : ∀ b ∈ l, m + 1 ≤ b := by
      intro b hb
      have := hhead b hb
      omega
    have hr : (1 : ℚ) / a ≤ 1 / m :=
      one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast ha)
    exact add_le_add hr (ih (Nat.succ_pos m) htail ht)

/-- A finite search whose negative answers will be justified for all denominators. -/
def possible : ℕ → ℕ → ℚ → Bool
  | 0, _, r => decide (r = 0)
  | k + 1, m, r =>
    if r ≤ 0 then false
    else if envelope (k + 1) m < r then false
    else decide (∃ d ∈ Finset.Icc m ⌊((k + 1 : ℕ) : ℚ) / r⌋₊,
      possible k (d + 1) (r - 1 / (d : ℚ)) = true)

/-- Every actual representation survives the search, including arbitrarily large denominators. -/
theorem possible_of_rep (l : List ℕ) {m : ℕ} (hm : 0 < m)
    (hs : l.Pairwise (· < ·)) (hlo : ∀ a ∈ l, m ≤ a) :
    possible l.length m (recips l) = true := by
  induction l generalizing m with
  | nil => simp [possible]
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    have ha : m ≤ a := hlo a (by simp)
    have ha0 : 0 < a := lt_of_lt_of_le hm ha
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha0
    have hr : 0 < recips (a :: l) := by
      rw [recips_cons]
      exact add_pos_of_pos_of_nonneg (div_pos zero_lt_one haQ) (recips_nonneg l)
    have he := recips_le_envelope (a :: l) hm (List.pairwise_cons.mpr ⟨hhead, htail⟩) hlo
    have hu : recips (a :: l) ≤ ((a :: l).length : ℚ) / a :=
      recips_le_uniform (a :: l) ha0 (by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact le_rfl
        · exact (hhead b hb).le)
    have hb : a ≤ ⌊((a :: l).length : ℚ) / recips (a :: l)⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ hr).mpr
      have := (le_div_iff₀ haQ).mp hu
      nlinarith
    change possible (l.length + 1) m (recips (a :: l)) = true
    rw [possible.eq_def]
    dsimp only
    simp only [List.length_cons] at he hb
    simp only [not_le_of_gt hr, not_lt_of_ge he, ite_false, decide_eq_true_eq]
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha, hb⟩, ?_⟩
    have ht : ∀ b ∈ l, a + 1 ≤ b := by
      intro b hb
      have := hhead b hb
      omega
    have heq : recips (a :: l) - 1 / (a : ℚ) = recips l := by simp
    rw [heq]
    exact ih (Nat.succ_pos a) htail ht

/-- Positive answers also produce genuine increasing denominator lists. -/
theorem rep_of_possible (k : ℕ) {m : ℕ} {r : ℚ} (hm : 0 < m)
    (h : possible k m r = true) :
    ∃ l : List ℕ, l.length = k ∧ l.Pairwise (· < ·) ∧
      (∀ a ∈ l, m ≤ a) ∧ recips l = r := by
  induction k generalizing m r with
  | zero =>
    have hr : r = 0 := of_decide_eq_true h
    exact ⟨[], rfl, by simp, by simp, by simp [hr]⟩
  | succ k ih =>
    rw [possible.eq_def] at h
    dsimp only at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · obtain ⟨a, ha, hp⟩ := of_decide_eq_true h
        obtain ⟨l, hlen, hs, hlo, hsum⟩ := ih (Nat.succ_pos a) hp
        refine ⟨a :: l, by simp [hlen], ?_, ?_, ?_⟩
        · exact List.pairwise_cons.mpr ⟨fun b hb => by
            have := hlo b hb
            omega, hs⟩
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact (Finset.mem_Icc.mp ha).1
          · have := hlo b hb
            have := (Finset.mem_Icc.mp ha).1
            omega
        · rw [recips_cons, hsum]
          ring

theorem recips_sort (A : Finset ℕ) :
    recips A.sort = ∑ a ∈ A, (1 : ℚ) / a := by
  simpa only [Finset.sort_toFinset, recips] using
    (List.sum_toFinset (fun a : ℕ => (1 : ℚ) / a) (A.sort_nodup (· ≤ ·))).symm

/-- Certificate soundness for ordinary finite sets, with no upper denominator bound. -/
theorem possible_of_finset (A : Finset ℕ) {k m : ℕ} {r : ℚ}
    (hm : 0 < m) (hk : A.card = k) (hlo : ∀ a ∈ A, m ≤ a)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = r) : possible k m r = true := by
  have h := possible_of_rep A.sort hm A.sortedLT_sort.pairwise
    (fun a ha => hlo a ((Finset.mem_sort (· ≤ ·)).mp ha))
  simpa only [Finset.length_sort, hk, recips_sort, hsum] using h

/-- The algorithm decides the actual finite-set representation problem. -/
theorem possible_iff_finset (k m : ℕ) (r : ℚ) (hm : 0 < m) :
    possible k m r = true ↔ ∃ A : Finset ℕ, A.card = k ∧
      (∀ a ∈ A, m ≤ a) ∧ (∑ a ∈ A, (1 : ℚ) / a) = r := by
  constructor
  · intro hp
    obtain ⟨l, hk, hs, hlo, hsum⟩ := rep_of_possible k hm hp
    have hn : l.Nodup := hs.nodup
    refine ⟨l.toFinset, ?_, ?_, ?_⟩
    · simpa [List.toFinset_card_of_nodup hn] using hk
    · intro a ha
      exact hlo a (List.mem_toFinset.mp ha)
    · rw [List.sum_toFinset _ hn]
      exact hsum
  · rintro ⟨A, hk, hlo, hsum⟩
    exact possible_of_finset A hm hk hlo hsum

/-- A reusable proof rule: a false certificate implies a sharpness upper bound. -/
theorem has_small_denominator (k M : ℕ) (hcert : possible k (M + 1) 1 = false)
    (A : Finset ℕ) (hk : A.card = k) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    ∃ a ∈ A, a ≤ M := by
  by_contra h
  push Not at h
  have ht := possible_of_finset A (Nat.succ_pos M) hk
    (fun a ha => by have := h a ha; omega) hsum
  rw [hcert] at ht
  contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem certificate_seven : possible 7 4 1 = false := by decide +kernel

/-- Possible values of the smallest denominator in a k-term representation of one. -/
def AttainableMinimum (k M : ℕ) : Prop :=
  ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a) ∧
    (∑ a ∈ A, (1 : ℚ) / a) = 1 ∧ M ∈ A ∧ (∀ a ∈ A, M ≤ a)

/-- Combines a universal impossibility certificate with an explicit attaining set. -/
theorem exact_of_certificate (k M : ℕ)
    (hcert : possible k (M + 1) 1 = false) (hw : AttainableMinimum k M) :
    IsGreatest {m | AttainableMinimum k m} M := by
  refine ⟨hw, ?_⟩
  intro m hm
  obtain ⟨A, hk, _, hsum, _, hlo⟩ := hm
  obtain ⟨a, ha, hle⟩ := has_small_denominator k M hcert A hk hsum
  exact (hlo a ha).trans hle

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem exact_three : IsGreatest {m | AttainableMinimum 3 m} 2 := by
  apply exact_of_certificate 3 2 (by decide +kernel)
  refine ⟨{2, 3, 6}, ?_⟩
  norm_num

theorem exact_four : IsGreatest {m | AttainableMinimum 4 m} 2 := by
  apply exact_of_certificate 4 2 (by decide +kernel)
  refine ⟨{2, 3, 7, 42}, ?_⟩
  norm_num

theorem exact_five : IsGreatest {m | AttainableMinimum 5 m} 3 := by
  apply exact_of_certificate 5 3 (by decide +kernel)
  refine ⟨{3, 4, 5, 6, 20}, ?_⟩
  norm_num

theorem exact_six : IsGreatest {m | AttainableMinimum 6 m} 3 := by
  apply exact_of_certificate 6 3 (by decide +kernel)
  refine ⟨{3, 4, 5, 6, 30, 60}, ?_⟩
  norm_num

theorem exact_seven : IsGreatest {m | AttainableMinimum 7 m} 3 := by
  apply exact_of_certificate 7 3 certificate_seven
  refine ⟨{3, 4, 5, 7, 30, 42, 60}, ?_⟩
  norm_num

theorem exact_eight : IsGreatest {m | AttainableMinimum 8 m} 4 := by
  apply exact_of_certificate 8 4 (by decide +kernel)
  refine ⟨{4, 5, 6, 7, 8, 15, 40, 42}, ?_⟩
  norm_num

theorem exact_nine : IsGreatest {m | AttainableMinimum 9 m} 4 := by
  apply exact_of_certificate 9 4 (by decide +kernel)
  refine ⟨{4, 5, 6, 7, 8, 20, 40, 42, 60}, ?_⟩
  norm_num

theorem exact_ten : IsGreatest {m | AttainableMinimum 10 m} 5 := by
  apply exact_of_certificate 10 5 (by decide +kernel)
  refine ⟨{5, 6, 7, 8, 9, 10, 12, 40, 42, 45}, ?_⟩
  norm_num

theorem exact_eleven : IsGreatest {m | AttainableMinimum 11 m} 6 := by
  apply exact_of_certificate 11 6 (by decide +kernel)
  refine ⟨{6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28}, ?_⟩
  norm_num

theorem exact_twelve : IsGreatest {m | AttainableMinimum 12 m} 6 := by
  apply exact_of_certificate 12 6 (by decide +kernel)
  refine ⟨{6, 7, 8, 9, 10, 11, 12, 18, 22, 33, 40, 42}, ?_⟩
  norm_num

end UnitFractionBounds

#print axioms UnitFractionBounds.recips_le_envelope
#print axioms UnitFractionBounds.possible_of_rep
#print axioms UnitFractionBounds.rep_of_possible
#print axioms UnitFractionBounds.possible_of_finset
#print axioms UnitFractionBounds.certificate_seven
#print axioms UnitFractionBounds.possible_iff_finset
#print axioms UnitFractionBounds.exact_three
#print axioms UnitFractionBounds.exact_four
#print axioms UnitFractionBounds.exact_five
#print axioms UnitFractionBounds.exact_six
#print axioms UnitFractionBounds.exact_seven
#print axioms UnitFractionBounds.exact_eight
#print axioms UnitFractionBounds.exact_nine
#print axioms UnitFractionBounds.exact_ten
#print axioms UnitFractionBounds.exact_eleven
#print axioms UnitFractionBounds.exact_twelve
