/-
Copyright (c) 2026. Released under the Apache 2.0 license.

An additive geometric-arclength extension for JSP-000926 / Erdos 1115.
Prepared with OpenAI Codex assistance.

The entire-function construction and alternating-gate proof are due to the
pinned plby/lean-proofs formalization (formal authors Codex and GPT-5.6 Sol),
following Gol'dberg and Eremenko. The gate-hitting argument below is adapted
from its labyrinth_isLengthBarrier; the new conclusion uses actual variation
of arbitrary continuous curves, without a speed or parametrization assumption.
-/
import JSP000926.Upstream
import Mathlib.Topology.EMetricSpace.BoundedVariation

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace Erdos1115

/-- Ordered, interior-disjoint compact subarcs contained in the open disk.
Sharing an endpoint is harmless: an endpoint has zero arclength. -/
def DiscSubarcs (gamma : ℝ → ℂ) (r : ℝ) {n : ℕ}
    (a b : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ a i ∧ a i ≤ b i ∧
    ∀ t ∈ Set.Icc (a i) (b i), ‖gamma t‖ < r) ∧
  ∀ i j, i < j → b i ≤ a j

/-- Geometric length in an open disk, with multiplicity: the supremum of sums
of subarc lengths over finite ordered disjoint compact subarcs in the disk.
Each subarc length is Mathlib's total variation, i.e. the supremum of polygonal
chord sums. In particular no time parameter or speed bound occurs, and infinite
length stays infinite (there is no conversion of infinity to zero). -/
noncomputable def geometricLengthInDisc (gamma : ℝ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (a : Fin n → ℝ), ⨆ (b : Fin n → ℝ),
    ⨆ (_ : DiscSubarcs gamma r a b),
    ∑ i : Fin n, eVariationOn gamma (Set.Icc (a i) (b i))

/-- The usual eventual linear upper bound for the nonnegative extended length. -/
def HasLinearGeometricLength (gamma : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in atTop,
    geometricLengthInDisc gamma r ≤ ENNReal.ofReal (C * r)

lemma subarc_variation_le_geometricLengthInDisc {gamma : ℝ → ℂ}
    {r a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hinside : ∀ t ∈ Set.Icc a b, ‖gamma t‖ < r) :
    eVariationOn gamma (Set.Icc a b) ≤ geometricLengthInDisc gamma r := by
  have hfamily : DiscSubarcs gamma r (fun _ : Fin 1 ↦ a) (fun _ ↦ b) := by
    constructor
    · intro i
      exact ⟨ha, hab, hinside⟩
    · intro i j hij
      exact (not_lt_of_ge (by omega : j ≤ i) hij).elim
  unfold geometricLengthInDisc
  refine le_iSup_of_le 1 (le_iSup_of_le (fun _ : Fin 1 ↦ a)
    (le_iSup_of_le (fun _ : Fin 1 ↦ b) (le_iSup_of_le hfamily ?_)))
  simp

/-- Genuine geometric wall condition; the curve need only be continuous. -/
def IsGeometricLengthBarrier (S : Set ℂ) (inner outer cost : ℝ) : Prop :=
  ∀ gamma : ℝ → ℂ, Continuous gamma →
    Tendsto (fun t ↦ ‖gamma t‖) atTop atTop →
    ∀ t₀ : ℝ, 0 ≤ t₀ → ‖gamma t₀‖ < inner →
    (∀ t ≥ t₀, gamma t ∉ S) →
    ENNReal.ofReal cost ≤ geometricLengthInDisc gamma outer

def HasGeometricEscapingBarriers (f : ℂ → ℂ) : Prop :=
  ∃ (S : ℕ → Set ℂ) (inner outer cost : ℕ → ℝ),
    (∀ n, 0 < outer n) ∧
    Tendsto inner atTop atTop ∧
    Tendsto outer atTop atTop ∧
    Tendsto (fun n ↦ cost n / outer n) atTop atTop ∧
    ∀ n, (∀ z ∈ S n, ‖f z‖ ≤ 1) ∧
      IsGeometricLengthBarrier (S n) (inner n) (outer n) (cost n)

theorem labyrinth_isGeometricLengthBarrier (k : ℕ) {T : ℝ} (hT : 0 < T) :
    IsGeometricLengthBarrier (labyrinthSet k T) (2 * T) (3 * T)
      (2 * (k - 1 : ℕ) * T) := by
  intro γ hcontinuous hescape t₀ ht₀ hstart havoid
  by_cases hk : k ≤ 1
  · have hkzero : k - 1 = 0 := Nat.sub_eq_zero_of_le hk
    simp [hkzero]
  have hk2 : 2 ≤ k := Nat.lt_of_not_ge hk
  have hcont : Continuous (fun t ↦ ‖γ t‖) := hcontinuous.norm
  have hhits : ∀ i : ℕ, ∃ t : ℝ,
      t₀ < t ∧ ‖γ t‖ = T * gateRadius k i ∧
        ∀ u : ℝ, t₀ ≤ u → u < t → ‖γ u‖ < T * gateRadius k i := by
    intro i
    apply exists_first_hitting_time hcont
    · have : 2 * T ≤ T * gateRadius k i := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (two_le_gateRadius k i) hT.le
      linarith
    · exact hescape
  choose t ht₀t hnormt hbefore using hhits
  have ht_mono : ∀ {i j : ℕ}, i < j → t i < t j := by
    intro i j hij
    have hradlt : T * gateRadius k i < T * gateRadius k j := by
      have hkpos : 0 < (k + 1 : ℝ) := by positivity
      have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      simp only [gateRadius]
      apply mul_lt_mul_of_pos_left _ hT
      have := (div_lt_div_iff_of_pos_right hkpos).2 hijR
      linarith
    by_contra hnot
    have hji : t j ≤ t i := le_of_not_gt hnot
    rcases hji.eq_or_lt with heq | hlt
    · have := (hnormt i).symm.trans (heq ▸ hnormt j)
      linarith
    · have hsmall := hbefore i (t j) (ht₀t j).le hlt
      rw [hnormt j] at hsmall
      linarith
  have hsigned : ∀ {i : ℕ}, i < k →
      T < ((-1 : ℝ) ^ i) * (γ (t i)).re := by
    intro i hi
    have hnotgate : γ (t i) ∉ labyrinthGate k i T := by
      intro hgate
      exact havoid (t i) (ht₀t i).le (by
        simp only [labyrinthSet, Set.mem_iUnion]
        exact ⟨i, Finset.mem_range.mpr hi, hgate⟩)
    have hnotle : ¬ ((-1 : ℝ) ^ i) * (γ (t i)).re ≤ T * gateRadius k i / 2 := by
      intro hle
      apply hnotgate
      exact ⟨hnormt i, hle⟩
    have hrad : 2 * T ≤ T * gateRadius k i := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (two_le_gateRadius k i) hT.le
    exact lt_of_le_of_lt (by linarith) (lt_of_not_ge hnotle)
  have hstep : ∀ i : ℕ, i < k - 1 → ENNReal.ofReal (2 * T) ≤ edist (γ (t (i + 1))) (γ (t i)) := by
    intro i hi
    have hiK : i < k := lt_of_lt_of_le hi (Nat.sub_le k 1)
    have hisK : i + 1 < k := by omega
    have hti : t i < t (i + 1) := ht_mono (Nat.lt_succ_self i)
    have hx := hsigned hiK
    have hy := hsigned hisK
    have hsignsucc : ((-1 : ℝ) ^ (i + 1)) = -((-1 : ℝ) ^ i) := by
      rw [pow_succ]
      ring
    rw [hsignsucc] at hy
    have hreal : 2 * T <
        ((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re) := by
      change 2 * T < ((-1 : ℝ) ^ i) * ((γ (t i)).re - (γ (t (i + 1))).re)
      nlinarith
    have habssign : |((-1 : ℝ) ^ i)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    have habs : 2 * T < |(γ (t i) - γ (t (i + 1))).re| := by
      have hpos : 0 < ((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re) :=
        lt_trans (by positivity) hreal
      calc
        2 * T < |((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re)| := by
          rwa [abs_of_pos hpos]
        _ = |(γ (t i) - γ (t (i + 1))).re| := by rw [abs_mul, habssign, one_mul]
    have hnorm : 2 * T < ‖γ (t i) - γ (t (i + 1))‖ :=
      lt_of_lt_of_le habs (Complex.abs_re_le_norm _)
    simpa only [edist_dist, dist_eq_norm, norm_sub_rev] using
      ENNReal.ofReal_le_ofReal hnorm.le
  have hlastK : k - 1 < k := Nat.sub_lt (by omega) (by omega)
  have ht0last : t 0 ≤ t (k - 1) := (ht_mono (by omega)).le
  have hinterval : Set.Icc (t 0) (t (k - 1)) ⊆
      {u : ℝ | 0 ≤ u ∧ ‖γ u‖ < 3 * T} := by
    intro u hu
    refine ⟨le_trans ht₀ (le_trans (ht₀t 0).le hu.1), ?_⟩
    rcases hu.2.eq_or_lt with heq | hlt
    · subst u
      rw [hnormt]
      simpa [mul_comm] using mul_lt_mul_of_pos_left (gateRadius_bounds hlastK).2 hT
    · have hu₀ : t₀ ≤ u := le_trans (ht₀t 0).le hu.1
      have hsmall := hbefore (k - 1) u hu₀ hlt
      exact lt_trans hsmall (by
        simpa [mul_comm] using mul_lt_mul_of_pos_left (gateRadius_bounds hlastK).2 hT)
  have hvariation : ENNReal.ofReal (2 * (k - 1 : ℕ) * T) ≤
      eVariationOn γ (Set.Icc (t 0) (t (k - 1))) := by
    calc
      ENNReal.ofReal (2 * (k - 1 : ℕ) * T) =
          ∑ i ∈ Finset.range (k - 1), ENNReal.ofReal (2 * T) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ by positivity)]
        congr 1
        simp
        ring
      _ ≤ ∑ i ∈ Finset.range (k - 1), edist (γ (t (i + 1))) (γ (t i)) :=
        Finset.sum_le_sum fun i hi ↦ hstep i (Finset.mem_range.mp hi)
      _ ≤ eVariationOn γ (Set.Icc (t 0) (t (k - 1))) := by
        apply eVariationOn.sum_le_of_monotoneOn_Iic
        · intro i hi j hj hij
          exact (show StrictMono t from fun i j hij ↦ ht_mono hij).monotone hij
        · intro i hi
          exact ⟨(show Monotone t from fun i j hij ↦
            (lt_or_eq_of_le hij).elim (fun h ↦ (ht_mono h).le) (fun h ↦ h ▸ le_rfl))
              (Nat.zero_le i),
            (lt_or_eq_of_le hi).elim (fun h ↦ (ht_mono h).le) (fun h ↦ h ▸ le_rfl)⟩
  exact hvariation.trans (subarc_variation_le_geometricLengthInDisc
    (le_trans ht₀ (ht₀t 0).le) ht0last (fun u hu ↦ (hinterval hu).2))

lemma counterexampleFunction_hasGeometricEscapingBarriers (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    HasGeometricEscapingBarriers (counterexampleFunction φ hφ) := by
  let T : ℕ → ℝ := fun n ↦ (constructionStage φ hφ n).T
  refine ⟨(fun n ↦ labyrinthSet (n + 2) (T n)),
    (fun n ↦ 2 * T n), (fun n ↦ 3 * T n),
    (fun n ↦ 2 * (n + 2 - 1 : ℕ) * T n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact mul_pos (by norm_num) (constructionStage φ hφ n).T_pos
  · exact Filter.Tendsto.const_mul_atTop (by norm_num) (constructionStage_T_tendsto φ hφ)
  · exact Filter.Tendsto.const_mul_atTop (by norm_num) (constructionStage_T_tendsto φ hφ)
  · have hnat : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
      by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hlim := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 3) hnat
    apply hlim.congr'
    filter_upwards with n
    have hTne : T n ≠ 0 := (constructionStage φ hφ n).T_pos.ne'
    change (constructionStage φ hφ n).T ≠ 0 at hTne
    simp only [T]
    rw [show n + 2 - 1 = n + 1 by omega]
    push_cast
    field_simp
  · intro n
    constructor
    · intro z hz
      exact counterexampleFunction_wall φ hφ n hz
    · exact labyrinth_isGeometricLengthBarrier (n + 2) (constructionStage φ hφ n).T_pos

/-- Increasing geometric wall costs exclude linear disk length without any
Lipschitz, differentiability, unit-speed or rectifiability hypothesis. -/
theorem not_hasLinearGeometricLength_of_hasGeometricEscapingBarriers
    {f : ℂ → ℂ} (hf : HasGeometricEscapingBarriers f)
    {gamma : ℝ → ℂ} (hcontinuous : Continuous gamma)
    (hescape : EscapesAlong f gamma) : ¬HasLinearGeometricLength gamma := by
  rintro ⟨C, hC, hlinear⟩
  obtain ⟨S, inner, outer, cost, houterpos, hinner, houter, hratio, hwall⟩ := hf
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1
    (hescape.2.eventually (eventually_gt_atTop 1))
  let t₁ : ℝ := max t₀ 0
  have hO : ∀ᶠ n : ℕ in atTop,
      geometricLengthInDisc gamma (outer n) ≤ ENNReal.ofReal (C * outer n) :=
    houter.eventually hlinear
  have hinside : ∀ᶠ n : ℕ in atTop, ‖gamma t₁‖ < inner n :=
    hinner.eventually (eventually_gt_atTop ‖gamma t₁‖)
  have hlarge : ∀ᶠ n : ℕ in atTop, C < cost n / outer n :=
    hratio.eventually (eventually_gt_atTop C)
  obtain ⟨n, hnO, hninside, hnlarge⟩ := (hO.and (hinside.and hlarge)).exists
  have hcost : ENNReal.ofReal (cost n) ≤ geometricLengthInDisc gamma (outer n) :=
    (hwall n).2 gamma hcontinuous hescape.1 t₁ (le_max_right _ _) hninside (by
      intro t ht hmem
      exact (not_lt_of_ge ((hwall n).1 _ hmem))
        (ht₀ t (le_trans (le_max_left _ _) ht)))
  have hle : cost n ≤ C * outer n :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (houterpos n).le)).mp
      (hcost.trans hnO)
  have hstrict : C * outer n < cost n := (lt_div_iff₀ (houterpos n)).mp hnlarge
  exact (not_lt_of_ge hle) hstrict

/-- Gol'dberg--Eremenko's counterexample with intrinsic geometric disk length
and arbitrary continuous parametrizations. Local rectifiability is allowed but
not required: curves of infinite disk length also fail the linear bound. -/
theorem not_erdos_1115_geometric :
    ∀ phi : ℝ → ℝ, Tendsto phi atTop atTop →
      ∃ f : ℂ → ℂ,
        (∃ z w : ℂ, f z ≠ f w) ∧
        ¬Bornology.IsBounded (Set.range f) ∧
        EntireOfFiniteOrder f ∧
        HasGolbergEremenkoGrowth phi f ∧
        HasGeometricEscapingBarriers f ∧
        ∀ gamma : ℝ → ℂ, Continuous gamma → EscapesAlong f gamma →
          ¬HasLinearGeometricLength gamma := by
  intro phi hphi
  let psi := slowGrowth phi
  let hpsi : Tendsto psi atTop atTop := slowGrowth_tendsto hphi
  let f := counterexampleFunction psi hpsi
  have hbarriers : HasGeometricEscapingBarriers f :=
    counterexampleFunction_hasGeometricEscapingBarriers psi hpsi
  refine ⟨f, counterexampleFunction_nonconstant psi hpsi,
    counterexampleFunction_range_unbounded psi hpsi,
    counterexampleFunction_finiteOrder_of_slowGrowth phi hphi,
    counterexampleFunction_hasGrowth_of_slowGrowth phi hphi, hbarriers, ?_⟩
  intro gamma hcontinuous hescape
  exact not_hasLinearGeometricLength_of_hasGeometricEscapingBarriers
    hbarriers hcontinuous hescape

#print axioms labyrinth_isGeometricLengthBarrier
#print axioms not_erdos_1115_geometric

end Erdos1115
