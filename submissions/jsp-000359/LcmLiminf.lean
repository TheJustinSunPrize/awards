import LcmCounting
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# JSP-000359 / Erdos 440: sharp lower limit and full real-threshold statement

The historical result is attributed to Erdos and Szemeredi (1980).
This is an AI-assisted formalization, not a claim of mathematical novelty.

The reciprocal-LCM estimate telescopes over any finite tail subset. If every
large square threshold had count greater than its square root, a finite greedy
selection would violate that estimate. Hence square thresholds with count at
most their square root occur arbitrarily far out. Consecutive natural numbers
attain lower limit one. The final theorem combines this with the order bound.

Reference: https://www.erdosproblems.com/440
-/

set_option autoImplicit false

namespace JSP000359

open Finset

theorem reciprocal_lcm_le {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    (1 : ℝ) / Nat.lcm a b ≤ 1 / (a : ℝ) - 1 / (b : ℝ) := by
  have hb : 0 < b := by omega
  have hl : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have hd : Nat.gcd a b ≤ b - a :=
    Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))
  have hprod : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have hdiff : (Nat.gcd a b : ℝ) ≤ (b : ℝ) - a := by
    have hnat : Nat.gcd a b + a ≤ b := by omega
    have : (Nat.gcd a b : ℝ) + a ≤ b := by exact_mod_cast hnat
    linarith
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hlr : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast hl
  apply (div_le_iff₀ hlr).2
  field_simp
  apply (le_div_iff₀ (mul_pos har hbr)).2
  have hmul := mul_le_mul_of_nonneg_right hdiff (le_of_lt hlr)
  nlinarith

theorem reciprocal_sum_interval (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) {n m : ℕ} (hnm : n ≤ m) :
    (∑ i ∈ Ico n m, (1 : ℝ) / Nat.lcm (a i) (a (i + 1))) ≤
      1 / (a n : ℝ) - 1 / (a m : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Ico n m, ((1 : ℝ) / a i - 1 / a (i + 1)) := by
      apply sum_le_sum
      intro i _
      exact reciprocal_lcm_le (hpos i) (ha (Nat.lt_succ_self i))
    _ = _ := by
      have h := sum_Ico_sub (fun i => (1 : ℝ) / a i) hnm
      simp only [sum_sub_distrib] at h ⊢
      linarith

theorem reciprocal_sum_tail (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (s : Finset ℕ) (n : ℕ)
    (hs : ∀ i ∈ s, n ≤ i) :
    (∑ i ∈ s, (1 : ℝ) / Nat.lcm (a i) (a (i + 1))) ≤ 1 / ((n : ℝ) + 1) := by
  let m := max n (s.sup id + 1)
  have hnm : n ≤ m := le_max_left _ _
  have hsub : s ⊆ Ico n m := by
    intro i hi
    apply mem_Ico.mpr
    have hib : i ≤ s.sup id := le_sup (f := id) hi
    have hmax : s.sup id + 1 ≤ m := le_max_right _ _
    exact ⟨hs i hi, by omega⟩
  have han := ha.add_le_nat n 0
  simp only [Nat.add_zero] at han
  have hzero := hpos 0
  have han' : (n : ℝ) + 1 ≤ a n := by exact_mod_cast (show n + 1 ≤ a n by omega)
  calc
    _ ≤ ∑ i ∈ Ico n m, (1 : ℝ) / Nat.lcm (a i) (a (i + 1)) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 1 / (a n : ℝ) - 1 / (a m : ℝ) := reciprocal_sum_interval a ha hpos hnm
    _ ≤ 1 / (a n : ℝ) := sub_le_self _ (by positivity)
    _ ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) han'

theorem greedy_tail (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (n : ℕ)
    (hc : ∀ k ≥ n, k < (goodIndices a (k ^ 2)).card) (m : ℕ) :
    ∃ s : Finset ℕ, s.card = m ∧ (∀ i ∈ s, n ≤ i) ∧
      (∑ j ∈ range m, (1 : ℝ) / ((n + j : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ s, (1 : ℝ) / Nat.lcm (a i) (a (i + 1)) := by
  induction m with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨s, hcard, htail, hsum⟩ := ih
    have hecard : (range n ∪ s).card ≤ n + m := by
      calc
        _ ≤ (range n).card + s.card := card_union_le _ _
        _ = _ := by simp [hcard]
    have hcount := hc (n + m) (by omega)
    obtain ⟨i, higood, hinot⟩ := exists_mem_not_mem_of_card_lt_card
      (lt_of_le_of_lt hecard hcount)
    have hins : i ∉ s := fun hi => hinot (mem_union.mpr (Or.inr hi))
    have hin : n ≤ i := by
      have hi : i ∉ range n := fun hi => hinot (mem_union.mpr (Or.inl hi))
      simpa using hi
    have hl : Nat.lcm (a i) (a (i + 1)) ≤ (n + m) ^ 2 :=
      (mem_goodIndices_iff a ha hpos i _).mp higood
    have hlr : (Nat.lcm (a i) (a (i + 1)) : ℝ) ≤ ((n + m : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hl
    have hlpos : (0 : ℝ) < Nat.lcm (a i) (a (i + 1)) := by
      exact_mod_cast Nat.lcm_pos (hpos i) (hpos (i + 1))
    have hweight := one_div_le_one_div_of_le hlpos hlr
    refine ⟨insert i s, by simp [hins, hcard], ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact hin
      · exact htail j hj
    · rw [sum_insert hins, sum_range_succ]
      linarith

theorem inverse_square_lower (t : ℝ) (ht : 0 < t) :
    1 / t - 1 / (t + 1) ≤ 1 / t ^ 2 := by
  have ht1 : 0 < t + 1 := by linarith
  calc
    _ = 1 / (t * (t + 1)) := by
      field_simp [ne_of_gt ht, ne_of_gt ht1]
    _ ≤ 1 / t ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos ht) (by nlinarith)

theorem inverse_square_sum_lower (n m : ℕ) (hn : 0 < n) :
    (1 : ℝ) / n - 1 / ((n + m : ℕ) : ℝ) ≤
      ∑ j ∈ range m, (1 : ℝ) / ((n + j : ℕ) : ℝ) ^ 2 := by
  calc
    _ = ∑ j ∈ range m, ((1 : ℝ) / (n + j : ℕ) - 1 / (n + (j + 1) : ℕ)) := by
      have h := sum_range_sub (fun j => (1 : ℝ) / (n + j : ℕ)) m
      simp only [Nat.add_zero, sum_sub_distrib] at h ⊢
      linarith
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      have ht : (0 : ℝ) < (n + j : ℕ) := by exact_mod_cast (show 0 < n + j by omega)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using inverse_square_lower _ ht

/-- Arbitrarily large square thresholds have count at most their square root. -/
theorem cofinal_square_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (N : ℕ) :
    ∃ k ≥ N, (goodIndices a (k ^ 2)).card ≤ k := by
  by_contra h
  push_neg at h
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have hc : ∀ k ≥ n, k < (goodIndices a (k ^ 2)).card := by
    intro k hk
    exact h k ((le_max_left _ _).trans hk)
  obtain ⟨s, _, htail, hsum⟩ := greedy_tail a ha hpos n hc (n * n + 1)
  have hu := reciprocal_sum_tail a ha hpos s n htail
  have hl := inverse_square_sum_lower n (n * n + 1) hn
  have hb := hl.trans (hsum.trans hu)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hb
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgap : (1 : ℝ) / n - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
    field_simp [ne_of_gt hnr, ne_of_gt hn1]
  have hs : (1 : ℝ) / ((n : ℝ) + (n * n + 1)) < 1 / ((n : ℝ) * (n + 1)) :=
    one_div_lt_one_div_of_lt (mul_pos hnr hn1) (by nlinarith)
  linarith

def consecutiveNaturals (i : ℕ) : ℕ := i + 1

theorem consecutiveNaturals_strictMono : StrictMono consecutiveNaturals := by
  intro i j h
  exact Nat.add_lt_add_right h 1

theorem consecutiveNaturals_pos (i : ℕ) : 0 < consecutiveNaturals i := Nat.succ_pos i

theorem consecutive_lcm (i : ℕ) :
    Nat.lcm (consecutiveNaturals i) (consecutiveNaturals (i + 1)) = (i + 1) * (i + 2) := by
  have h : Nat.Coprime (i + 1) ((i + 1) + 1) := by simp
  simpa [consecutiveNaturals, Nat.add_assoc] using h.lcm_eq_mul

theorem consecutive_count_bounds (x : ℕ) :
    Nat.sqrt x - 1 ≤ (goodIndices consecutiveNaturals x).card ∧
      (goodIndices consecutiveNaturals x).card ≤ Nat.sqrt x := by
  constructor
  · calc
      _ = (range (Nat.sqrt x - 1)).card := by simp
      _ ≤ _ := card_le_card (by
        intro i hi
        have hi' := mem_range.mp hi
        apply (mem_goodIndices_iff consecutiveNaturals consecutiveNaturals_strictMono
          consecutiveNaturals_pos i x).mpr
        rw [consecutive_lcm]
        have hsq := Nat.sqrt_le' x
        have hi2 : i + 2 ≤ Nat.sqrt x := by omega
        nlinarith)
  · calc
      _ ≤ (range (Nat.sqrt x)).card := card_le_card (by
        intro i hi
        have hl := (mem_goodIndices_iff consecutiveNaturals consecutiveNaturals_strictMono
          consecutiveNaturals_pos i x).mp hi
        rw [consecutive_lcm] at hl
        apply mem_range.mpr
        have hsq := Nat.lt_succ_sqrt' x
        nlinarith)
      _ = _ := by simp

noncomputable def realCount (a : ℕ → ℕ) (x : ℝ) : ℕ :=
  (goodIndices a ⌊x⌋₊).card

noncomputable def normalizedCount (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  realCount a x / Real.sqrt x

theorem mem_real_count_iff (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    i ∈ goodIndices a ⌊x⌋₊ ↔ (Nat.lcm (a i) (a (i + 1)) : ℝ) ≤ x := by
  rw [mem_goodIndices_iff a ha hpos, Nat.le_floor_iff hx]

theorem real_counting_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (x : ℝ) (hx : 0 ≤ x) :
    (realCount a x : ℝ) ≤ 2 * Real.sqrt x := by
  have h : (realCount a x : ℝ) ≤ 2 * (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    exact_mod_cast counting_bound_sqrt a ha hpos ⌊x⌋₊
  have hs : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le hx))
  linarith

open Filter
open scoped Topology

theorem normalized_liminf_le_one (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) :
    Filter.liminf (normalizedCount a) atTop ≤ 1 := by
  have hf : ∃ᶠ x : ℝ in atTop, normalizedCount a x ≤ 1 := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n, hn⟩ := exists_nat_gt N
    obtain ⟨k, hk, hc⟩ := cofinal_square_bound a ha hpos (max n 1)
    have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
    have hkn : n ≤ k := (le_max_left _ _).trans hk
    have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    refine ⟨((k ^ 2 : ℕ) : ℝ), ?_, ?_⟩
    · have hnk : (n : ℝ) ≤ k := by exact_mod_cast hkn
      have h1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      push_cast
      nlinarith
    · unfold normalizedCount realCount
      rw [Nat.floor_natCast, Nat.cast_pow, Real.sqrt_sq (le_of_lt hkr)]
      apply (div_le_iff₀ hkr).2
      simpa using (show ((goodIndices a (k ^ 2)).card : ℝ) ≤ k by exact_mod_cast hc)
  refine liminf_le_of_frequently_le hf ?_
  refine ⟨0, ?_⟩
  change ∀ᶠ x : ℝ in atTop, 0 ≤ normalizedCount a x
  exact Filter.Eventually.of_forall (fun x => by
    unfold normalizedCount
    positivity)

theorem consecutive_real_count_bounds (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x - 2 ≤ (realCount consecutiveNaturals x : ℝ) ∧
      (realCount consecutiveNaturals x : ℝ) ≤ Real.sqrt x := by
  obtain ⟨hlo, hhi⟩ := consecutive_count_bounds ⌊x⌋₊
  have hnat : Nat.sqrt ⌊x⌋₊ ≤ realCount consecutiveNaturals x + 1 := by
    unfold realCount
    omega
  have hlow : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ (realCount consecutiveNaturals x : ℝ) + 1 := by
    exact_mod_cast hnat
  have hsquare : x < ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) ^ 2 := by
    have h := (Nat.floor_lt hx).mp (Nat.lt_succ_sqrt' ⌊x⌋₊)
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using h
  have hsqrt : Real.sqrt x < (Nat.sqrt ⌊x⌋₊ : ℝ) + 1 := by
    exact (Real.sqrt_lt hx (by positivity)).mpr hsquare
  constructor
  · linarith
  · have hhi' : (realCount consecutiveNaturals x : ℝ) ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) := by
      exact_mod_cast hhi
    exact hhi'.trans (Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le hx)))

theorem consecutive_normalized_bounds (x : ℝ) (hx : 0 < x) :
    1 - 2 / Real.sqrt x ≤ normalizedCount consecutiveNaturals x ∧
      normalizedCount consecutiveNaturals x ≤ 1 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  obtain ⟨hlo, hhi⟩ := consecutive_real_count_bounds x hx.le
  unfold normalizedCount
  constructor
  · apply (le_div_iff₀ hs).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hs)]
    exact hlo
  · exact (div_le_one hs).mpr hhi

theorem real_sqrt_tendsto_atTop : Tendsto Real.sqrt atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨(max b 0) ^ 2, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
  exact (le_max_left _ _).trans ((Real.le_sqrt (le_max_right _ _) hx0).mpr hx)

theorem consecutive_normalized_tendsto :
    Tendsto (normalizedCount consecutiveNaturals) atTop (𝓝 1) := by
  have hz : Tendsto (fun x : ℝ => 2 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp real_sqrt_tendsto_atTop))
  have hl : Tendsto (fun x : ℝ => 1 - 2 / Real.sqrt x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  have hb : ∀ᶠ x : ℝ in atTop,
      1 - 2 / Real.sqrt x ≤ normalizedCount consecutiveNaturals x ∧
        normalizedCount consecutiveNaturals x ≤ 1 :=
    (eventually_gt_atTop (0 : ℝ)).mono (fun x hx => consecutive_normalized_bounds x hx)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- The greatest possible lower limit in the original problem is exactly one. -/
theorem sharp_liminf :
    IsGreatest {c : ℝ | ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      Filter.liminf (normalizedCount a) atTop = c} 1 := by
  constructor
  · exact ⟨consecutiveNaturals, consecutiveNaturals_strictMono, consecutiveNaturals_pos,
      consecutive_normalized_tendsto.liminf_eq⟩
  · intro c hc
    obtain ⟨a, ha, hpos, rfl⟩ := hc
    exact normalized_liminf_le_one a ha hpos

theorem normalized_count_bounded (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (x : ℝ) :
    0 ≤ normalizedCount a x ∧ normalizedCount a x ≤ 2 := by
  constructor
  · unfold normalizedCount
    positivity
  · by_cases hx : 0 < x
    · exact (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mpr (real_counting_bound a ha hpos x hx.le)
    · simp [normalizedCount, Real.sqrt_eq_zero_of_nonpos (by linarith : x ≤ 0)]

/-- Both questions in the original problem, with real thresholds and standard liminf. -/
theorem original_problem :
    (∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
      ∀ (x : ℝ), 0 ≤ x → (realCount a x : ℝ) ≤ 2 * Real.sqrt x) ∧
    IsGreatest {c : ℝ | ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      Filter.liminf (normalizedCount a) atTop = c} 1 := by
  exact ⟨real_counting_bound, sharp_liminf⟩

#print axioms mem_real_count_iff
#print axioms normalized_count_bounded
#print axioms sharp_liminf
#print axioms original_problem

end JSP000359
