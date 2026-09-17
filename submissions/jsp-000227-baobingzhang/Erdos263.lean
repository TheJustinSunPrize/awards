import Mathlib

/-!
# Erdős Problem 263: `⌊α ^ 2 ^ n⌋₊` is an irrationality sequence for all but countably many `α`

A nondecreasing sequence `a` of positive integers is a (weak, or "Type 2") irrationality sequence
if `∑ 1 / b n` is irrational for every sequence `b` of positive integers with `a n / b n → 1`.
Koizumi [Ko25, Theorem 4] proved that `⌊α ^ 2 ^ n⌋` is such a sequence for all `α > 1` outside a
countable set. This file proves that theorem:

* `Erdos263.erdos_263.variants.doubly_exponential_all_but_countable :
    ∀ᶠ (α : ℝ) in .cocountable, α > 1 →
      IsWeakIrrationalitySequence (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊)`.

The definition `IsWeakIrrationalitySequence` and the statement of
`erdos_263.variants.doubly_exponential_all_but_countable` (category "research solved") are copied
verbatim, with their docstrings, from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/263.lean`, Apache-2.0), with the same namespace and name.

Conventions. `∀ᶠ α in cocountable, P α` means that `{α | ¬ P α}` is a countable subset of `ℝ`.
Sequences are indexed from `n = 0`. Koizumi starts at `n = 1`; the two versions are equivalent,
because adding or removing the single term `1 / b 0` does not change irrationality. In
Lean, `∑'` of a non-summable series is `0`, which is rational, so the proof shows that every
admissible `b` has a summable reciprocal series before using the value of the sum.

## Proof

Let `α > 1`, `X n = α ^ 2 ^ n` and `a n = ⌊X n⌋₊`. Then `a n ≥ 1` and `a` is monotone, so if the
sequence is not a weak irrationality sequence, there is `b` with `b n > 0`, `a n / b n → 1` and
`∑' 1 / b n = q` for some `q : ℚ`.

* **Growth of `b`** (`tendsto_and_recoveryCond`). Since `⌊x⌋₊ / x → 1`, `b n / X n → 1`, so
  `b n → ∞`, and `X (n + 1) = X n ^ 2` gives `b n ^ 2 / b (n + 1) → 1`. Hence from some `N` on,
  `b n ≥ 4` and `b n ^ 2 ≤ 2 b (n + 1)`, so `b (n + 1) ≥ 2 b n` and `1 / b (j + n) ≤ 2⁻ʲ / b n`.
  This gives summability and the tail bound `t n ≤ 2 / b n`, where `t n = ∑' j, 1 / b (j + n)`.
* **Recovery of `b n` from the sum** (Koizumi's Theorem 1 with `β = 1`, limit form). With
  `t n = 1 / b n + t (n + 1)`: `b n t (n + 1) ≤ 2 b n / b (n + 1) ≤ 4 / b n → 0`, so
  `b n t n → 1` and `b n ^ 2 t (n + 1) = (b n ^ 2 / b (n + 1)) (b (n + 1) t (n + 1)) → 1`. The
  identity `(t n)⁻¹ + 1 - b n = (1 + b n t (n + 1) - b n ^ 2 t (n + 1)) / (b n t n)` then gives
  `(t n)⁻¹ + 1 - b n → 0`. As `t n = q - ∑_{k < n} 1 / b k`, from some `M` on, `b n` is the
  natural number within `1 / 2` of `(q - ∑_{k < n} 1 / b k)⁻¹ + 1` (`RecoveryCond M q b`).
* **Countably many such `b`** (`eq_of_recoveryCond`, `countable_recoverable`). By strong
  induction, `b` is determined by `M`, `q` and `b 0, …, b (M - 1)`, since two natural numbers
  within `1 / 2` of the same real number are equal. So for fixed `M` and `q` the map
  `b ↦ (b k)_{k < M}` into the countable type `Fin M → ℕ` is injective, and the union over
  `M : ℕ` and `q : ℚ` is countable.
* **`b` determines `α`** (`subsingleton_base`). If `b n / α ^ 2 ^ n → 1` and
  `b n / β ^ 2 ^ n → 1` with `1 < α < β`, then `(β / α) ^ 2 ^ n → 1`, but it tends to `∞`.
* **Conclusion.** The exceptional set is contained in `⋃_{b ∈ S} {α > 1 | b n / α ^ 2 ^ n → 1}`,
  where `S` is the countable set of positive `b` satisfying some `RecoveryCond M q` with `q : ℚ`
  and every set in the union has at most one element.

## What is not covered

Only the case of Koizumi's Theorem 1 needed here is proved: the limit form with `β = 1`, for `b`
asymptotic to `⌊α ^ 2 ^ n⌋₊`. Its explicit version (`β ≥ 0`,
`|a n ^ 2 / a (n + 1) - β| ≤ 1/3`, threshold `a n ≥ 8 (β + 1/3) ^ 2`) and Corollaries 2 and 3
(Sylvester sequence, Millin series) are not formalized. The strictly increasing predicate
`IsIrrationalitySequence` of formal-conjectures is not claimed (it fails for `1 < α < 4/3`, where
`a 0 = a 1 = 1`). The questions of Erdős Problem 263 itself (`erdos_263.parts.i`, whether
`2 ^ 2 ^ n` is an irrationality sequence, and `erdos_263.parts.ii`) remain open and are not proved
here.

## References

* [Ko25] Koizumi, J., _Irrationality of the reciprocal sum of doubly exponential sequences_.
  arXiv:2504.05933 (2025).
* [erdosproblems.com/263](https://www.erdosproblems.com/263)
-/

open Filter
open scoped Topology

namespace Erdos263

/-- The nondecreasing version of `IsIrrationalitySequence`, as used by Koizumi [Ko25]: the sequence
is positive and nondecreasing, and every positive sequence asymptotic to it has irrational
reciprocal sum. -/
def IsWeakIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    Monotone a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/-- From index `N` on, each `b n` is the natural number nearest to
`(q - ∑_{k < n} 1 / b k)⁻¹ + 1`. -/
def RecoveryCond (N : ℕ) (q : ℝ) (b : ℕ → ℕ) : Prop :=
  ∀ n, N ≤ n → |(q - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + 1 - b n| < 1 / 2

/-- A sequence satisfying `RecoveryCond N q` is determined by `q` and its first `N` terms. -/
theorem eq_of_recoveryCond {N : ℕ} {q : ℝ} {b b' : ℕ → ℕ} (hb : RecoveryCond N q b)
    (hb' : RecoveryCond N q b') (h : ∀ k < N, b k = b' k) : b = b' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · exact h n hn
    · push Not at hn
      have hs : ∑ k ∈ Finset.range n, 1 / (b k : ℝ) = ∑ k ∈ Finset.range n, 1 / (b' k : ℝ) :=
        Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
      have h1 := hb n hn
      have h2 := hb' n hn
      rw [hs] at h1
      rw [abs_lt] at h1 h2
      have e1 : (b n : ℝ) < b' n + 1 := by linarith
      have e2 : (b' n : ℝ) < b n + 1 := by linarith
      have e1' : b n < b' n + 1 := by exact_mod_cast e1
      have e2' : b' n < b n + 1 := by exact_mod_cast e2
      omega

/-- Only countably many sequences satisfy `RecoveryCond N q` for some `N` and rational `q`. -/
theorem countable_recoverable :
    {b : ℕ → ℕ | ∃ (N : ℕ) (q : ℚ), RecoveryCond N q b}.Countable := by
  have : {b : ℕ → ℕ | ∃ (N : ℕ) (q : ℚ), RecoveryCond N q b} =
      ⋃ N : ℕ, ⋃ q : ℚ, {b | RecoveryCond N q b} := by
    ext b; simp
  rw [this]
  refine Set.countable_iUnion fun N => Set.countable_iUnion fun q => ?_
  refine Set.MapsTo.countable_of_injOn (f := fun b : ℕ → ℕ => fun k : Fin N => b k)
    (Set.mapsTo_univ _ _) ?_ Set.countable_univ
  intro b hb b' hb' hbb
  exact eq_of_recoveryCond hb hb' fun k hk => congrFun hbb ⟨k, hk⟩

/-- A positive sequence `b` is asymptotic to `α ^ 2 ^ n` for at most one `α > 1`. -/
theorem subsingleton_base (b : ℕ → ℕ) (hb : ∀ n, 0 < b n) :
    {α : ℝ | 1 < α ∧ Tendsto (fun n : ℕ => (b n : ℝ) / α ^ 2 ^ n) atTop (𝓝 1)}.Subsingleton := by
  have key : ∀ α β : ℝ, 1 < α → α < β →
      Tendsto (fun n : ℕ => (b n : ℝ) / α ^ 2 ^ n) atTop (𝓝 1) →
      Tendsto (fun n : ℕ => (b n : ℝ) / β ^ 2 ^ n) atTop (𝓝 1) → False := by
    intro α β hα hαβ hA hB
    have hq : 1 < β / α := (one_lt_div (by linarith)).mpr hαβ
    have h2 : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) one_lt_two
    have hinf : Tendsto (fun n : ℕ => (β / α) ^ 2 ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hq).comp h2
    have hlim : Tendsto (fun n : ℕ => ((b n : ℝ) / α ^ 2 ^ n) / ((b n : ℝ) / β ^ 2 ^ n)) atTop
        (𝓝 (1 / 1)) := hA.div hB one_ne_zero
    rw [div_one] at hlim
    refine not_tendsto_nhds_of_tendsto_atTop hinf 1 (hlim.congr fun n => ?_)
    have : (b n : ℝ) ≠ 0 := by exact_mod_cast (hb n).ne'
    have hα0 : α ^ 2 ^ n ≠ 0 := pow_ne_zero _ (by linarith)
    have hβ0 : β ^ 2 ^ n ≠ 0 := pow_ne_zero _ (by linarith)
    rw [div_pow]
    field_simp
  intro α ⟨hα, hA⟩ β ⟨hβ, hB⟩
  rcases lt_trichotomy α β with h | h | h
  · exact (key α β hα h hA hB).elim
  · exact h
  · exact (key β α hβ h hB hA).elim

/-- If `α > 1` and `b` is a positive sequence with `⌊α ^ 2 ^ n⌋₊ / b n → 1`, then
`b n / α ^ 2 ^ n → 1`, and from some index on `b n` is recovered from `∑' n, 1 / b n` and the
earlier terms (Koizumi's Theorem 1 with `β = 1`, limit form). -/
theorem tendsto_and_recoveryCond (α : ℝ) (hα : 1 < α) (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)
    (hab : Tendsto (fun n : ℕ => (⌊α ^ 2 ^ n⌋₊ : ℝ) / (b n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (b n : ℝ) / α ^ 2 ^ n) atTop (𝓝 1) ∧
      ∃ N, RecoveryCond N (∑' n, 1 / (b n : ℝ)) b := by
  set X : ℕ → ℝ := fun n => α ^ 2 ^ n with hXdef
  have hXpos : ∀ n, 0 < X n := fun n => pow_pos (by linarith) _
  have hX1 : ∀ n, 1 ≤ X n := fun n => one_le_pow₀ hα.le
  have hXsq : ∀ n, X (n + 1) = X n ^ 2 := fun n => by
    simp only [hXdef, pow_succ, pow_mul]
  have hXtop : Tendsto X atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hα).comp
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) one_lt_two)
  have hapos : ∀ n, (0 : ℝ) < ⌊X n⌋₊ := fun n => by
    exact_mod_cast Nat.floor_pos.mpr (hX1 n)
  have hbpos : ∀ n, (0 : ℝ) < b n := fun n => by exact_mod_cast hb n
  have hg : Tendsto (fun n => (⌊X n⌋₊ : ℝ) / X n) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hXtop
  have hu : Tendsto (fun n => (b n : ℝ) / X n) atTop (𝓝 1) := by
    have : Tendsto (fun n => ((⌊X n⌋₊ : ℝ) / X n) / ((⌊X n⌋₊ : ℝ) / (b n : ℝ))) atTop
        (𝓝 (1 / 1)) := hg.div hab one_ne_zero
    rw [div_one] at this
    refine this.congr fun n => ?_
    have := (hapos n).ne'
    have := (hbpos n).ne'
    have := (hXpos n).ne'
    field_simp
  have hbtop : Tendsto (fun n => (b n : ℝ)) atTop atTop := by
    refine (hu.pos_mul_atTop one_pos hXtop).congr fun n => ?_
    have := (hXpos n).ne'
    field_simp
  have hc : Tendsto (fun n => (b n : ℝ) ^ 2 / b (n + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun n => ((b n : ℝ) / X n) ^ 2 / ((b (n + 1) : ℝ) / X (n + 1))) atTop
        (𝓝 (1 ^ 2 / 1)) := (hu.pow 2).div (hu.comp (tendsto_add_atTop_nat 1)) one_ne_zero
    rw [one_pow, div_one] at this
    refine this.congr fun n => ?_
    rw [hXsq n]
    have := (hbpos n).ne'
    have := (hbpos (n + 1)).ne'
    have := (hXpos n).ne'
    field_simp
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (4 : ℝ) ≤ b n ∧ (b n : ℝ) ^ 2 / b (n + 1) ≤ 2 := by
    have h1 := hbtop.eventually_ge_atTop 4
    have h2 := hc.eventually (ge_mem_nhds (show (1 : ℝ) < 2 by norm_num))
    exact eventually_atTop.mp (h1.and h2)
  have hgrow : ∀ n ≥ N, (b n : ℝ) ^ 2 ≤ 2 * b (n + 1) := fun n hn => by
    have := (hN n hn).2
    rw [div_le_iff₀ (hbpos (n + 1))] at this
    linarith
  have hdouble : ∀ n ≥ N, 2 * (b n : ℝ) ≤ b (n + 1) := fun n hn => by
    have h4 := (hN n hn).1
    have := hgrow n hn
    nlinarith
  have hgeom : ∀ n ≥ N, ∀ j, 2 ^ j * (b n : ℝ) ≤ b (j + n) := by
    intro n hn j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hdouble (j + n) (by omega)
      rw [show j + 1 + n = j + n + 1 by ring, pow_succ]
      nlinarith
  have hterm : ∀ n ≥ N, ∀ j, 1 / (b (j + n) : ℝ) ≤ (1 / 2) ^ j * (1 / b n) := by
    intro n hn j
    calc 1 / (b (j + n) : ℝ) ≤ 1 / (2 ^ j * b n) :=
          one_div_le_one_div_of_le (by have := hbpos n; positivity) (hgeom n hn j)
      _ = (1 / 2) ^ j * (1 / b n) := by
          rw [one_div_pow, one_div_mul_one_div]
  have hsumN : Summable (fun j => 1 / (b (j + N) : ℝ)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) (hterm N le_rfl)
      (summable_geometric_two.mul_right _)
  have hsum : Summable (fun n => 1 / (b n : ℝ)) := (summable_nat_add_iff N).mp hsumN
  set t : ℕ → ℝ := fun n => ∑' j, 1 / (b (j + n) : ℝ) with htdef
  have htsum : ∀ n, Summable (fun j => 1 / (b (j + n) : ℝ)) := fun n =>
    (summable_nat_add_iff n).mpr hsum
  have hsplit : ∀ n, ∑ k ∈ Finset.range n, 1 / (b k : ℝ) + t n = ∑' n, 1 / (b n : ℝ) :=
    fun n => hsum.sum_add_tsum_nat_add n
  have hstep : ∀ n, t n = 1 / b n + t (n + 1) := by
    intro n
    simp only [htdef]
    rw [(htsum n).tsum_eq_zero_add, zero_add]
    congr 1
    exact tsum_congr fun j => by rw [show j + 1 + n = j + (n + 1) by ring]
  have htnonneg : ∀ n, 0 ≤ t n := fun n => tsum_nonneg fun j => by positivity
  have htle : ∀ n ≥ N, t n ≤ 2 * (1 / b n) := by
    intro n hn
    calc t n ≤ ∑' j, (1 / 2 : ℝ) ^ j * (1 / b n) :=
          Summable.tsum_le_tsum (hterm n hn) (htsum n) (summable_geometric_two.mul_right _)
      _ = 2 * (1 / b n) := by rw [tsum_mul_right, tsum_geometric_two]
  have hL5 : Tendsto (fun n => (b n : ℝ) * t (n + 1)) atTop (𝓝 0) := by
    have h4 : Tendsto (fun n => (4 : ℝ) / b n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hbtop
    refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (hbpos n).le (htnonneg _))
      ?_ h4
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 := htle (n + 1) (by omega)
    have h2 := hgrow n hn
    have hbn := hbpos n
    have hbn1 := hbpos (n + 1)
    calc (b n : ℝ) * t (n + 1) ≤ b n * (2 * (1 / b (n + 1))) :=
          mul_le_mul_of_nonneg_left h1 hbn.le
      _ = 2 * b n / b (n + 1) := by field_simp
      _ ≤ 4 / b n := by
          rw [div_le_div_iff₀ hbn1 hbn]
          nlinarith
  have hL6 : Tendsto (fun n => (b n : ℝ) * t n) atTop (𝓝 1) := by
    have := hL5.const_add 1
    rw [add_zero] at this
    refine this.congr fun n => ?_
    rw [hstep n, mul_add, mul_one_div_cancel (hbpos n).ne']
  have hL7 : Tendsto (fun n => (b n : ℝ) ^ 2 * t (n + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun n => (b n : ℝ) ^ 2 / b (n + 1) * ((b (n + 1) : ℝ) * t (n + 1))) atTop
        (𝓝 (1 * 1)) := hc.mul (hL6.comp (tendsto_add_atTop_nat 1))
    rw [one_mul] at this
    refine this.congr fun n => ?_
    have := (hbpos (n + 1)).ne'
    field_simp
  have hL8 : Tendsto (fun n => (t n)⁻¹ + 1 - b n) atTop (𝓝 0) := by
    have : Tendsto (fun n => (1 + (b n : ℝ) * t (n + 1) - (b n : ℝ) ^ 2 * t (n + 1)) /
        ((b n : ℝ) * t n)) atTop (𝓝 ((1 + 0 - 1) / 1)) :=
      ((hL5.const_add 1).sub hL7).div hL6 one_ne_zero
    rw [add_zero, sub_self, zero_div] at this
    refine this.congr fun n => ?_
    have hB := hbpos n
    have hT := htnonneg (n + 1)
    have hne : (1 : ℝ) / b n + t (n + 1) ≠ 0 := by
      have := one_div_pos.mpr hB
      linarith
    rw [hstep n]
    field_simp
    ring
  refine ⟨hu, ?_⟩
  have hev := (hL8.abs).eventually (gt_mem_nhds (show |(0 : ℝ)| < 1 / 2 by norm_num))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨M, fun n hn => ?_⟩
  rw [← hsplit n, add_sub_cancel_left]
  exact hM n hn

/--
Koizumi [Ko25] showed that $a_n = \lfloor \alpha^{2^n} \rfloor$ is an irrationality sequence
for all but countably many $\alpha > 1$, in the nondecreasing sense `IsWeakIrrationalitySequence`.
The strictly increasing predicate would fail on the whole interval $1 < \alpha < 4/3$, where
$a_0 = a_1 = 1$.

[Ko25] Koizumi, J., Irrationality of the reciprocal sum of doubly exponential sequences,
       arXiv:2504.05933 (2025).
-/
theorem erdos_263.variants.doubly_exponential_all_but_countable :
    ∀ᶠ (α : ℝ) in .cocountable, α > 1 →
      IsWeakIrrationalitySequence (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊) := by
  rw [Filter.eventually_iff, Filter.mem_cocountable]
  have hS : {b : ℕ → ℕ | (∀ n, 0 < b n) ∧ ∃ (N : ℕ) (q : ℚ), RecoveryCond N q b}.Countable :=
    countable_recoverable.mono fun b hb => hb.2
  refine (hS.biUnion fun b hb => (subsingleton_base b hb.1).countable).mono ?_
  intro α hα
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_imp] at hα
  obtain ⟨hα1, hnot⟩ := hα
  have hpos : ∀ n : ℕ, ⌊α ^ 2 ^ n⌋₊ > 0 := fun n => Nat.floor_pos.mpr (one_le_pow₀ hα1.le)
  have hmono : Monotone (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊) := fun m n hmn =>
    Nat.floor_le_floor (pow_le_pow_right₀ hα1.le (Nat.pow_le_pow_right two_pos hmn))
  have hnot' : ¬ ∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (⌊α ^ 2 ^ n⌋₊ : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)) := fun h => hnot ⟨hpos, hmono, h⟩
  push Not at hnot'
  obtain ⟨b, ⟨hb, hab⟩, hirr⟩ := hnot'
  simp only [Irrational, Set.mem_range, not_not] at hirr
  obtain ⟨q, hq⟩ := hirr
  obtain ⟨hu, N, hN⟩ := tendsto_and_recoveryCond α hα1 b hb hab
  refine Set.mem_biUnion (x := b) ⟨hb, N, q, ?_⟩ ⟨hα1, hu⟩
  rw [hq]
  exact hN

end Erdos263
