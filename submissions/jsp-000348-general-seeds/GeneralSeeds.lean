/-
Copyright (c) 2026 green3sf. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: green3sf (AI-assisted development)
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Arbitrary positive seeds for consecutive-sum sequences

An elementary formalization of the arbitrary-seed qualitative result in
Tang, arXiv:2603.09939v2, Section 6.1. The main theorem uses only eventual
strict increase and eventual generation by consecutive earlier blocks;
greedy minimality is not needed. Indices here start at zero.

The parity obstruction and finite-approximation existence/uniqueness construction
adapt patterns from baobingzhang, Erdos423.lean, commit
6af50e76fc7d7bf6da0c43975998805fca5cb4a3 (Apache-2.0). They are changed here to
zero-based arbitrary seeds and half-open blocks. See NOTICE and PRIOR_ART.md.
The consecutive-tail contradiction uses one odd-exponent power of two and
adjacent products, rather than the earlier file's two-power plateau argument.
-/

open Finset
namespace GeneralSeeds

/-- A sum of at least two consecutive earlier terms. The right endpoint is excluded. -/
def BlockSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃ p q, p + 1 < q ∧ q ≤ n ∧ m = ∑ i ∈ Ico p q, a i

/-- A subtraction-free version convenient for arbitrary starting and ending indices. -/
theorem twice_interval (a : ℕ → ℕ) (n₀ T p q : ℕ) (hp : n₀ ≤ p) (hpq : p ≤ q)
    (h : ∀ i, n₀ ≤ i → i < q → a i = T + (i - n₀)) :
    2 * (∑ i ∈ Ico p q, a i) + (T + (p - n₀)) * (T + (p - n₀)) +
      (T + (q - n₀)) =
      (T + (q - n₀)) * (T + (q - n₀)) + (T + (p - n₀)) := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [sum_Ico_succ_top (by omega)]
    have hi := ih (fun i hi hiq => h i hi (by omega))
    rw [h q (by omega) (by omega)]
    have he : q + 1 - n₀ = q - n₀ + 1 := by omega
    rw [he]
    nlinarith

/-- A power of two cannot be a sum of two or more consecutive positive integers. -/
theorem power_two_obstruction (r x d : ℕ) (hx : 0 < x) (hd : 2 ≤ d)
    (he : 2 * 2 ^ r + x * x + (x + d) = (x + d) * (x + d) + x) : False := by
  have hprod : d * (2 * x + d - 1) = 2 ^ (r + 1) := by
    have ht : 1 ≤ 2 * x + d := by omega
    have ht' := Nat.sub_add_cancel ht
    rw [pow_succ]
    nlinarith
  rcases Nat.even_or_odd d with ⟨u, hu⟩ | ho
  · have ho : Odd (2 * x + d - 1) := ⟨x + u - 1, by omega⟩
    have hdvd : (2 * x + d - 1) ∣ 2 ^ (r + 1) := Dvd.intro_left _ hprod
    have := Nat.Coprime.eq_one_of_dvd (ho.coprime_two_right.pow_right (r + 1)) hdvd
    omega
  · have hdvd : d ∣ 2 ^ (r + 1) := Dvd.intro _ hprod
    have := Nat.Coprime.eq_one_of_dvd (ho.coprime_two_right.pow_right (r + 1)) hdvd
    omega

/-- No eventually generated sequence can have an eventually consecutive positive tail. -/
theorem no_consecutive_tail (a : ℕ → ℕ) (s n₀ T : ℕ) (hs : s ≤ n₀) (hT : 0 < T)
    (hgen : ∀ n, s ≤ n → BlockSum a n (a n))
    (htail : ∀ n, n₀ ≤ n → a n = T + (n - n₀)) : False := by
  let S := ∑ i ∈ range n₀, a i
  let k := 2 * S + T * T + T + 2
  let X := 2 ^ (k + 1)
  let P := 2 ^ (2 * k + 1)
  have hX : k < X := by
    exact lt_trans (Nat.lt_succ_self _) (Nat.lt_two_pow_self)
  have hPX : 2 * P = X * X := by
    dsimp [P, X]
    rw [← pow_add]
    have he : (k + 1) + (k + 1) = (2 * k + 1) + 1 := by omega
    rw [he, pow_succ]
    omega
  have hXP : X ≤ P := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  have hSP : S < P := by dsimp [k] at hX; omega
  have hTP : T ≤ P := by dsimp [k] at hX; omega
  let n := n₀ + (P - T)
  have hn : n₀ ≤ n := Nat.le_add_right _ _
  have han : a n = P := by rw [htail n hn]; dsimp [n]; omega
  obtain ⟨p, q, hpq, hqn, hsum⟩ := hgen n (hs.trans hn)
  rw [han] at hsum
  have hq : n₀ < q := by
    by_contra hq
    have hsub : Ico p q ⊆ range n₀ := by
      intro i hi
      simp only [mem_Ico, mem_range] at *
      omega
    have := sum_le_sum_of_subset hsub (f := a)
    change (∑ i ∈ Ico p q, a i) ≤ S at this
    omega
  by_cases hp : n₀ ≤ p
  · have he := twice_interval a n₀ T p q hp (by omega) (fun i hi _ => htail i hi)
    rw [← hsum] at he
    have heq : T + (q - n₀) = (T + (p - n₀)) + (q - p) := by omega
    rw [heq] at he
    exact power_two_obstruction (2 * k + 1) (T + (p - n₀)) (q - p)
      (by omega) (by omega) he
  · let C := ∑ i ∈ Ico p n₀, a i
    have hCS : C ≤ S := sum_le_sum_of_subset (by
      intro i hi
      simp only [mem_Ico, mem_range] at *
      omega)
    have hsplit : P = C + ∑ i ∈ Ico n₀ q, a i := by
      rw [hsum]
      exact (sum_Ico_consecutive a (by omega) (by omega)).symm
    have he := twice_interval a n₀ T n₀ q le_rfl (by omega)
      (fun i hi _ => htail i hi)
    simp only [Nat.sub_self, add_zero] at he
    let v := T + (q - n₀) - 1
    have hv : T + (q - n₀) = v + 1 := by dsimp [v]; omega
    have hkey : v * (v + 1) + 2 * C + T = X * X + T * T := by
      rw [hv] at he
      nlinarith only [he, hPX, hsplit]
    have hx1 : T * T < X := by dsimp [k] at hX; omega
    have hx2 : 2 * S + T < X := by dsimp [k] at hX; omega
    rcases lt_or_ge v X with hvX | hvX
    · have h1 := Nat.mul_le_mul (show v ≤ X - 1 by omega) (show v + 1 ≤ X by omega)
      have h2 : X - 1 + 1 = X := by omega
      nlinarith only [hkey, h1, h2, hCS, hx2, Nat.zero_le (T*T)]
    · have h1 := Nat.mul_le_mul hvX (show X + 1 ≤ v + 1 by omega)
      nlinarith only [hkey, h1, hx1, Nat.zero_le (2*C + T)]

/-- Eventual strict increase gives a monotone excess above the index. -/
theorem tail_growth (a : ℕ → ℕ) (s : ℕ)
    (hstep : ∀ n, s ≤ n → a n < a (n + 1)) {i j : ℕ} (hi : s ≤ i) (hij : i ≤ j) :
    a i + (j - i) ≤ a j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have := hstep j (hi.trans hij)
    omega

/-- Every eventually increasing, eventually consecutive-block-generated positive sequence
has excess tending to infinity. Neither the seed values nor greedy minimality are prescribed. -/
theorem excess_tends_to_infinity (a : ℕ → ℕ) (s : ℕ)
    (hpos : ∀ n, 0 < a n)
    (hstep : ∀ n, s ≤ n → a n < a (n + 1))
    (hgen : ∀ n, s ≤ n → BlockSum a n (a n)) :
    ∀ M, ∃ N, ∀ n, N ≤ n → M + n ≤ a n := by
  classical
  let b : ℕ → ℕ := fun n => a (s + n) - n
  have hlo (n : ℕ) : n ≤ a (s + n) := by
    have := tail_growth a s hstep (i := s) (j := s + n) le_rfl (by omega)
    omega
  have hmono : Monotone b := by
    intro i j hij
    have := tail_growth a s hstep (i := s + i) (j := s + j) (by omega) (by omega)
    dsimp [b]
    have := hlo i
    have := hlo j
    omega
  have hunbounded : ∀ M, ∃ n, M ≤ b n := by
    intro M
    by_contra hc
    push Not at hc
    have hb : BddAbove (Set.range b) := ⟨M, by rintro _ ⟨n, rfl⟩; exact (hc n).le⟩
    have hf : (Set.range b).Finite := hb.finite
    obtain ⟨t, ht⟩ := (Set.range_nonempty b).csSup_mem hf
    have hmax (n : ℕ) : b n ≤ b t := by
      rw [ht]
      exact le_csSup hb ⟨n, rfl⟩
    have hconst (n : ℕ) (hn : t ≤ n) : b n = b t := le_antisymm (hmax n) (hmono hn)
    apply no_consecutive_tail a s (s + t) (a (s + t)) (by omega) (hpos _) hgen
    intro n hn
    have he := hconst (n - s) (by omega)
    have hnt : s + (n - s) = n := by omega
    dsimp [b] at he
    rw [hnt] at he
    have hnlo := hlo (n - s)
    rw [hnt] at hnlo
    have htlo := hlo t
    omega
  intro M
  obtain ⟨t, ht⟩ := hunbounded (M + s)
  refine ⟨s + t, fun n hn => ?_⟩
  have hb := hmono (show t ≤ n - s by omega)
  dsimp [b] at ht hb
  have hnlo := hlo (n - s)
  rw [show s + (n - s) = n by omega] at hb hnlo
  omega

/-- Infinitely many positive integers are absent from the entire range, including the seed. -/
theorem infinitely_many_omissions (a : ℕ → ℕ) (s : ℕ)
    (hpos : ∀ n, 0 < a n)
    (hstep : ∀ n, s ≤ n → a n < a (n + 1))
    (hgen : ∀ n, s ≤ n → BlockSum a n (a n)) :
    {m : ℕ | 0 < m ∧ m ∉ Set.range a}.Infinite := by
  classical
  intro hfin
  obtain ⟨K, hK⟩ := hfin.bddAbove
  obtain ⟨N, hN⟩ := excess_tends_to_infinity a s hpos hstep hgen (K + 3)
  let n := max N s
  have hnN : N ≤ n := le_max_left _ _
  have hns : s ≤ n := le_max_right _ _
  have hsize := hN n hnN
  have hcover : Icc (K + 1) (a n) ⊆ (range (n + 1)).image a := by
    intro x hx
    have hx' := mem_Icc.mp hx
    have hr : x ∈ Set.range a := by
      by_contra hr
      have := hK (show x ∈ {m : ℕ | 0 < m ∧ m ∉ Set.range a} from ⟨by omega, hr⟩)
      omega
    obtain ⟨i, rfl⟩ := hr
    apply mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    simp only [mem_range]
    by_contra hi
    have hg := tail_growth a s hstep hns (show n ≤ i by omega)
    omega
  have hc := card_le_card hcover
  have hi := card_image_le (s := range (n + 1)) (f := a)
  simp only [Nat.card_Icc, card_range] at hc hi
  omega

/-- The first `s` terms are the supplied seed; every later term is the least admissible
block sum strictly larger than its predecessor. The seed need not be sorted or distinct. -/
def IsGreedyExtension (seed : ℕ → ℕ) (s : ℕ) (a : ℕ → ℕ) : Prop :=
  (∀ i, i < s → a i = seed i) ∧
  ∀ n, s ≤ n → a (n - 1) < a n ∧ BlockSum a n (a n) ∧
    ∀ m, a (n - 1) < m → BlockSum a n m → a n ≤ m

theorem blockSum_congr {a b : ℕ → ℕ} {n m : ℕ} (h : ∀ i, i < n → a i = b i) :
    BlockSum a n m ↔ BlockSum b n m := by
  constructor <;> rintro ⟨p, q, hpq, hqn, hm⟩
  · refine ⟨p, q, hpq, hqn, hm.trans (sum_congr rfl fun i hi => ?_)⟩
    exact h i (lt_of_lt_of_le (mem_Ico.mp hi).2 hqn)
  · refine ⟨p, q, hpq, hqn, hm.trans (sum_congr rfl fun i hi => ?_)⟩
    exact (h i (lt_of_lt_of_le (mem_Ico.mp hi).2 hqn)).symm

noncomputable def next (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  sInf {m | a (n - 1) < m ∧ BlockSum a n m}

noncomputable def approximation (seed : ℕ → ℕ) (s : ℕ) : ℕ → ℕ → ℕ
  | 0 => seed
  | t + 1 => Function.update (approximation seed s t) (s + t) (next (approximation seed s t) (s + t))

noncomputable def greedy (seed : ℕ → ℕ) (s n : ℕ) : ℕ := approximation seed s (n + 1) n

theorem prefix_stable (seed : ℕ → ℕ) (s t i : ℕ) (hi : i < s + t) :
    ∀ u, t ≤ u → approximation seed s u i = approximation seed s t i := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    change Function.update _ (s + u) _ i = _
    rw [Function.update_of_ne (by omega), ih]

theorem greedy_eq_prefix (seed : ℕ → ℕ) (s t i : ℕ) (hi : i < s + t) :
    greedy seed s i = approximation seed s t i := by
  unfold greedy
  rcases le_total (i + 1) t with ht | ht
  · exact (prefix_stable seed s (i + 1) i (by omega) t ht).symm
  · exact prefix_stable seed s t i hi (i + 1) ht

theorem greedy_seed (seed : ℕ → ℕ) (s i : ℕ) (hi : i < s) :
    greedy seed s i = seed i := by
  exact greedy_eq_prefix seed s 0 i (by omega)

theorem greedy_step (seed : ℕ → ℕ) (s n : ℕ) (hs : 2 ≤ s) (hn : s ≤ n) :
    greedy seed s n = next (greedy seed s) n := by
  have h1 : greedy seed s n = next (approximation seed s (n - s)) n := by
    rw [greedy_eq_prefix seed s (n - s + 1) n (by omega)]
    simp only [approximation, show s + (n - s) = n by omega, Function.update_self]
  rw [h1, next, next]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  have hp : approximation seed s (n - s) (n - 1) = greedy seed s (n - 1) :=
    (greedy_eq_prefix seed s (n - s) (n - 1) (by omega)).symm
  rw [hp]
  exact and_congr_right fun _ => blockSum_congr fun i hi =>
    (greedy_eq_prefix seed s (n - s) i (by omega)).symm

/-- Existence for every positive seed of size at least two. -/
theorem greedy_is_extension (seed : ℕ → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hpos : ∀ i, i < s → 0 < seed i) : IsGreedyExtension seed s (greedy seed s) := by
  refine ⟨fun i hi => greedy_seed seed s i hi, fun n hn => ?_⟩
  have hzero : 0 < greedy seed s 0 := by rw [greedy_seed seed s 0 (by omega)]; exact hpos 0 (by omega)
  have hne : {m | greedy seed s (n - 1) < m ∧ BlockSum (greedy seed s) n m}.Nonempty := by
    refine ⟨∑ i ∈ range n, greedy seed s i, ?_, 0, n, by omega, le_rfl, ?_⟩
    · have hsub : ({0, n - 1} : Finset ℕ) ⊆ range n := by
        intro i hi
        simp only [mem_insert, mem_singleton, mem_range] at *
        omega
      have h := sum_le_sum_of_subset (f := greedy seed s) hsub
      rw [sum_pair (by omega)] at h
      omega
    · simp
  have hm := Nat.sInf_mem hne
  change _ < next (greedy seed s) n ∧ BlockSum _ n (next _ n) at hm
  rw [← greedy_step seed s n hs hn] at hm
  refine ⟨hm.1, hm.2, fun m hprev hblock => ?_⟩
  rw [greedy_step seed s n hs hn]
  exact Nat.sInf_le ⟨hprev, hblock⟩

/-- Greedy minimality determines every term, including all entries of the seed. -/
theorem extension_unique (seed : ℕ → ℕ) (s : ℕ) (hs : 2 ≤ s)
    {a b : ℕ → ℕ} (ha : IsGreedyExtension seed s a) (hb : IsGreedyExtension seed s b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < s
    · rw [ha.1 n hn, hb.1 n hn]
    · have hn' : s ≤ n := by omega
      have hp : a (n - 1) = b (n - 1) := ih (n - 1) (by omega)
      have hblock (m : ℕ) := blockSum_congr (a := a) (b := b) (n := n) (m := m) (fun i hi => ih i hi)
      obtain ⟨hap, hab, ham⟩ := ha.2 n hn'
      obtain ⟨hbp, hbb, hbm⟩ := hb.2 n hn'
      exact le_antisymm (ham _ (by omega) ((hblock _).mpr hbb))
        (hbm _ (by omega) ((hblock _).mp hab))

/-- There is exactly one infinite extension of every positive finite seed of length at least two. -/
theorem exists_unique_extension (seed : ℕ → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hpos : ∀ i, i < s → 0 < seed i) : ∃! a, IsGreedyExtension seed s a := by
  refine ⟨greedy seed s, greedy_is_extension seed s hs hpos, fun a ha => ?_⟩
  exact extension_unique seed s hs ha (greedy_is_extension seed s hs hpos)

/-- The complete arbitrary-positive-seed qualitative conclusion, for the actual greedy rule. -/
theorem arbitrary_seed_result (seed : ℕ → ℕ) (s : ℕ) (_hs : 2 ≤ s)
    (hseed : ∀ i, i < s → 0 < seed i) (a : ℕ → ℕ) (ha : IsGreedyExtension seed s a) :
    (∀ M, ∃ N, ∀ n, N ≤ n → M + n ≤ a n) ∧
    {m : ℕ | 0 < m ∧ m ∉ Set.range a}.Infinite := by
  have hpos (n : ℕ) : 0 < a n := by
    by_cases hn : n < s
    · rw [ha.1 n hn]; exact hseed n hn
    · have := (ha.2 n (by omega)).1; omega
  have hstep (n : ℕ) (hn : s ≤ n) : a n < a (n + 1) := by
    simpa using (ha.2 (n + 1) (by omega)).1
  have hgen (n : ℕ) (hn : s ≤ n) := (ha.2 n hn).2.1
  exact ⟨excess_tends_to_infinity a s hpos hstep hgen,
    infinitely_many_omissions a s hpos hstep hgen⟩

/-- Monotonicity of the signed excess on the increasing tail, in subtraction-free form. -/
theorem excess_monotone (a : ℕ → ℕ) (s : ℕ)
    (hstep : ∀ n, s ≤ n → a n < a (n + 1)) {i j : ℕ} (hi : s ≤ i) (hij : i ≤ j) :
    a i + j ≤ a j + i := by
  have := tail_growth a s hstep hi hij
  omega

/-- A direct conclusion for the constructed sequence, with no assumed infinite extension. -/
theorem constructed_sequence_result (seed : ℕ → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hseed : ∀ i, i < s → 0 < seed i) :
    (∀ M, ∃ N, ∀ n, N ≤ n → M + n ≤ greedy seed s n) ∧
    {m : ℕ | 0 < m ∧ m ∉ Set.range (greedy seed s)}.Infinite :=
  arbitrary_seed_result seed s hs hseed _ (greedy_is_extension seed s hs hseed)

end GeneralSeeds
