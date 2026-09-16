/-
This supplement preserves the third-party source attribution below.
It does not assert a new license over the adapted upstream argument.

JSP-000865 / Erdős 1042: extend the existing component-gap formalization to
zero transfinite diameter. Mathematical foundation: Ghosh--Ramachandran.
The component-gap argument below is adapted from plby/lean-proofs commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, ErdosProblems/Erdos1042.lean.
The upstream file and definitions are included unchanged in Upstream.lean.
This is an incremental boundary completion, not a first formalization.
-/
import JSP000865.Upstream

open scoped BigOperators ENNReal NNReal Topology
open Filter Metric Polynomial Set Topology MeasureTheory

noncomputable section
namespace Erdos1042

/-- A Fekete witness exists for every diameter below one, including zero.
The positive comparison level is chosen independently of the sign of `d`. -/
lemma exists_feketeDiameter_lt_one_including_zero {K : Set ℂ} {d : ℝ}
    (hdiam : HasTransfiniteDiameter K d) (hd₁ : d < 1) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧ feketeDiameter K m < q := by
  let q : ℝ := (max d 0 + 1) / 2
  have hmax : max d 0 < 1 := max_lt hd₁ zero_lt_one
  have hmax0 : 0 ≤ max d 0 := le_max_right _ _
  have hdmax : d ≤ max d 0 := le_max_left _ _
  have hdq : d < q := by dsimp [q]; linarith
  have hq₀ : 0 < q := by dsimp [q]; linarith
  have hq₁ : q < 1 := by dsimp [q]; linarith
  have hevent : ∀ᶠ m in atTop, feketeDiameter K m < q :=
    (tendsto_order.1 hdiam.2).2 q hdq
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 ≤ m := eventually_ge_atTop 2
  obtain ⟨m, hm, hmq⟩ := (hlarge.and hevent).exists
  exact ⟨m, hm, q, hq₀, hq₁, hmq⟩

/-- The existing uniform gap proof with its unnecessary `0 < d` hypothesis removed. -/
theorem hasUniformComponentGap_including_zero
    {K : Set ℂ} (hK : IsCompact K) {d : ℝ}
    (hdiam : HasTransfiniteDiameter K d) (hd₁ : d < 1) :
    HasUniformComponentGap K := by

  classical
  obtain ⟨m, hm, q, hq₀, hq₁, hmq⟩ :=
    exists_feketeDiameter_lt_one_including_zero hdiam hd₁
  obtain ⟨ε, hε, hprod⟩ :=
    exists_regularization_lt_one hK hm hq₀ hq₁ hmq
  by_contra hgap
  have hbad (k : ℕ) :
      ∃ n ≥ k + 1, ∃ z : Fin n → ℂ, (∀ i, z i ∈ K) ∧
        (1 - 1 / (k + 1 : ℝ)) * n <
          (componentCount (rootPolynomial z) : ℝ) := by
    by_contra hnone
    apply hgap
    refine ⟨1 / (k + 1 : ℝ), by positivity, k + 1, ?_⟩
    intro n hnlarge z hzK
    apply le_of_not_gt
    intro hviol
    apply hnone
    exact ⟨n, hnlarge, z, hzK, hviol⟩
  choose n hnlarge z hzK hzbad using hbad
  have hn : ∀ k, 0 < n k := fun k ↦ lt_of_lt_of_le (by omega) (hnlarge k)
  let zK : ∀ k, Fin (n k) → K := fun k i ↦ ⟨z k i, hzK k i⟩
  have hn_top : Tendsto n atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, fun k hk ↦ ?_⟩
    have hklarge := hnlarge k
    omega
  let hKcompact : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨μ, φ, hφmono, hμ⟩ := CompactSpace.tendsto_subseq
    (fun k ↦ empiricalProbability (hn k) (zK k))
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hnφtop : Tendsto (fun k ↦ n (φ k)) atTop atTop := hn_top.comp hφtop
  obtain ⟨c, hc, hgood⟩ := eventually_component_gap_of_tendsto_empirical
    hK hm hε hprod (fun k ↦ n (φ k)) (fun k ↦ hn (φ k)) hnφtop
    (fun k ↦ zK (φ k)) μ hμ
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / c)
  have hφlarge : ∀ᶠ k in atTop, N ≤ φ k := hφtop (eventually_ge_atTop N)
  obtain ⟨k, hgoodk, hφk⟩ := (hgood.and hφlarge).exists
  have hdenpos : (0 : ℝ) < φ k + 1 := by positivity
  have hrecip : 1 / (φ k + 1 : ℝ) < c := by
    apply (div_lt_iff₀ hdenpos).2
    have hcInv : c * (1 / c) = 1 := by field_simp
    have hNreal : (1 / c : ℝ) < N := hN
    have hNφ : (N : ℝ) ≤ φ k + 1 := by exact_mod_cast (hφk.trans (Nat.le_add_right _ _))
    nlinarith
  have hnreal : (0 : ℝ) < n (φ k) := by exact_mod_cast hn (φ k)
  have hcoeff :
      (1 - c) * n (φ k) <
        (1 - 1 / (φ k + 1 : ℝ)) * n (φ k) := by
    nlinarith
  exact (not_lt_of_ge hgoodk) (hcoeff.trans (hzbad (φ k)))

/-- The formerly omitted zero-capacity boundary, for arbitrary closed sets. -/
theorem zero_transfiniteDiameter_hasUniformComponentGap
    {K : Set ℂ} (hK : IsClosed K) (hd : HasTransfiniteDiameter K 0) :
    HasUniformComponentGap K := by
  exact hasUniformComponentGap_including_zero
    (isCompact_iff_isClosed_bounded.mpr ⟨hK, hd.1⟩) hd zero_lt_one

/-- Full subunit-capacity assertion using the literal `d < 1` range of the question. -/
theorem closed_subunit_transfiniteDiameter_hasUniformComponentGap
    {K : Set ℂ} (hK : IsClosed K) {d : ℝ}
    (hd : HasTransfiniteDiameter K d) (hd1 : d < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ z : Fin n → ℂ,
      (∀ i, z i ∈ K) →
        (componentCount (rootPolynomial z) : ℝ) ≤ (1 - c) * n := by
  exact hasUniformComponentGap_including_zero
    (isCompact_iff_isClosed_bounded.mpr ⟨hK, hd.1⟩) hd hd1

/-- The three existing resolution clauses, with the full subunit range restored. -/
theorem erdos_1042_including_zero :
    (∃ K : Set ℂ, IsClosed K ∧ HasTransfiniteDiameter K 1 ∧
      (¬ ∃ a : ℂ, K ⊆ closedBall a 1) ∧ HasInfinitelyManyMaximalLemniscates K) ∧
    (∀ K : Set ℂ, IsClosed K → ∀ d : ℝ, HasTransfiniteDiameter K d →
      d < 1 → HasUniformComponentGap K) ∧
    (∀ K : Set ℂ, IsClosed K → IsConnected K →
      ∀ d : ℝ, HasTransfiniteDiameter K d → d ≤ 1 / 4 →
        ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, z i ∈ K) →
          componentCount (rootPolynomial z) = 1) := by
  refine ⟨erdos_1042.1, ?_, erdos_1042.2.2⟩
  intro K hK d hd hd1
  exact closed_subunit_transfiniteDiameter_hasUniformComponentGap hK hd hd1

end Erdos1042

#print axioms Erdos1042.zero_transfiniteDiameter_hasUniformComponentGap
#print axioms Erdos1042.closed_subunit_transfiniteDiameter_hasUniformComponentGap
#print axioms Erdos1042.erdos_1042_including_zero
