import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Prime

/-!
Compatible-prime extension for reciprocal subset sums (JSP-000266 / Erdős 320).
The mathematical extension lemma is due to Bettin, Grenié, Molteni and Sanna,
A lower bound for the number of Egyptian fractions, arXiv:2509.10030v1, Lemma 4.
-/
open Finset
namespace ReciprocalDoubling

def Small (m : ℕ) (w : ℕ → ℤ) : Prop :=
  ∀ i ∈ Ico 1 m, -1 ≤ w i ∧ w i ≤ 1

def signedSum (m : ℕ) (w : ℕ → ℤ) : ℚ :=
  ∑ i ∈ Ico 1 m, (w i : ℚ) / i

def Irreducible (m : ℕ) : Prop :=
  0 < m ∧ ∀ w, Small m w → signedSum m w ≠ 1 / (m : ℚ)

def Compatible (m p : ℕ) : Prop :=
  ∀ w, Small m w → ¬(p : ℤ) ∣ (1 / (m : ℚ) - signedSum m w).num

/-- Nonzero sums of terms of positive valuation still have positive valuation. -/
theorem sum_val_pos {α : Type*} {p : ℕ} (hp : p.Prime)
    (s : Finset α) (f : α → ℚ)
    (hf : ∀ i ∈ s, f i = 0 ∨ 0 < padicValRat p (f i))
    (hs : ∑ i ∈ s, f i ≠ 0) : 0 < padicValRat p (∑ i ∈ s, f i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    rw [sum_insert ha] at hs ⊢
    have hf' := hf a (mem_insert_self a s)
    have hrest := fun i hi => hf i (mem_insert_of_mem hi)
    by_cases hzero : ∑ i ∈ s, f i = 0
    · simpa [hzero] using hf'.resolve_left (by simpa [hzero] using hs)
    · by_cases hfa : f a = 0
      · simpa [hfa] using ih hrest hzero
      · exact lt_of_lt_of_le (lt_min (hf'.resolve_left hfa) (ih hrest hzero))
          (padicValRat.min_le_padicValRat_add hs)

/-- Scaling a denominator not divisible by `p^k` leaves positive valuation. -/
theorem scaled_term_val {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hdiv : ¬p ^ k ∣ n) (z : ℤ) :
    (p : ℚ) ^ k * (z : ℚ) / n = 0 ∨
      0 < padicValRat p ((p : ℚ) ^ k * (z : ℚ) / n) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hz : z = 0
  · simp [hz]
  · right
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast hz
    have hval : padicValNat p n < k := by
      exact lt_of_not_ge (fun h => hdiv ((Nat.pow_dvd_iff_le_padicValNat hp.ne_one hn).2 h))
    rw [padicValRat.div (mul_ne_zero (pow_ne_zero k hp0) hz0) hn0,
      padicValRat.mul (pow_ne_zero k hp0) hz0, padicValRat.pow,
      padicValRat.self hp.one_lt, mul_one, padicValRat.of_int, padicValRat.of_nat]
    omega

/-- Multiples of a positive integer in an initial interval are a scaled interval. -/
theorem multiples_interval {m M : ℕ} (hM : 0 < M) :
    (Ico 1 (m * M)).filter (M ∣ ·) = (Ico 1 m).image (M * ·) := by
  ext n
  simp only [mem_filter, mem_Ico, mem_image]
  constructor
  · rintro ⟨⟨hn, hnm⟩, j, rfl⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · by_contra h
      have : j = 0 := by omega
      simp [this] at hn
    · nlinarith
  · rintro ⟨j, ⟨hj, hjm⟩, rfl⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, dvd_mul_right M j⟩

/-- Separating denominators divisible by the scale gives an exact rational identity. -/
theorem scaled_split {m M : ℕ} (hM : 0 < M) (w : ℕ → ℤ) :
    (M : ℚ) * signedSum (m * M) w =
      signedSum m (fun j => w (M * j)) +
      ∑ n ∈ (Ico 1 (m * M)).filter (fun n => ¬M ∣ n), (M : ℚ) * (w n : ℚ) / n := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  rw [signedSum, mul_sum]
  have split := sum_filter_add_sum_filter_not (Ico 1 (m * M)) (M ∣ ·)
    (fun n => (M : ℚ) * ((w n : ℚ) / n))
  rw [← split, multiples_interval hM, sum_image]
  · congr 1
    · unfold signedSum
      apply sum_congr rfl
      intro j hj
      have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Ico.mp hj).1)
      push_cast
      field_simp
    · apply sum_congr rfl
      intro n hn
      ring
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hM hab

/-- BGMS Lemma 4, with no restriction `m < p` and allowing `p` to divide `m`. -/
theorem compatible_prime_extension {m p k : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hc : Compatible m p) : Irreducible (m * p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  have hM : 0 < p ^ k := pow_pos hp.pos k
  refine ⟨Nat.mul_pos hm hM, ?_⟩
  intro w hw heq
  let v : ℕ → ℤ := fun j => w (p ^ k * j)
  have hv : Small m v := by
    intro j hj
    apply hw
    simp only [mem_Ico] at hj ⊢
    constructor <;> nlinarith
  have hnum := hc v hv
  let q : ℚ := 1 / (m : ℚ) - signedSum m v
  have hq : q ≠ 0 := by
    intro hz
    apply hnum
    change (p : ℤ) ∣ q.num
    simp [hz]
  have hlow : padicValRat p q ≤ 0 := by
    unfold padicValRat
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    simp
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hM0 : (p ^ k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hsplit := scaled_split (m := m) hM w
  rw [heq] at hsplit
  have hscale : (p ^ k : ℕ) / ((m * p ^ k : ℕ) : ℚ) = 1 / (m : ℚ) := by
    push_cast
    field_simp
  simp only [mul_one_div] at hsplit
  rw [hscale] at hsplit
  have hqsum : q = ∑ n ∈ (Ico 1 (m * p ^ k)).filter (fun n => ¬p ^ k ∣ n),
      (p : ℚ) ^ k * (w n : ℚ) / n := by
    dsimp [q, v]
    push_cast at hsplit
    linarith
  have hhigh : 0 < padicValRat p q := by
    rw [hqsum]
    apply sum_val_pos hp
    · intro n hn
      obtain ⟨hn, hnd⟩ := mem_filter.mp hn
      exact scaled_term_val hp (by have := (mem_Ico.mp hn).1; omega) hnd (w n)
    · rw [← hqsum]
      exact hq
  omega

/-- Sums of subsets of denominators strictly below `m`, including the empty sum. -/
def sumsBelow (m : ℕ) : Finset ℚ :=
  (Ico 1 m).powerset.image (fun a : Finset ℕ => ∑ i ∈ a, (1 : ℚ) / i)

/-- Every difference of two subset sums is a signed sum. -/
def differences (m : ℕ) : Finset ℚ :=
  ((sumsBelow m).product (sumsBelow m)).image (fun ab => ab.1 - ab.2)

/-- Signed sums are exactly differences of two reciprocal subset sums. -/
theorem mem_differences {m : ℕ} {q : ℚ} :
    q ∈ differences m ↔ ∃ w, Small m w ∧ signedSum m w = q := by
  constructor
  · intro h
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp h
    obtain ⟨a, ha, rfl⟩ := mem_image.mp (mem_product.mp hxy).1
    obtain ⟨b, hb, rfl⟩ := mem_image.mp (mem_product.mp hxy).2
    have ha' := mem_powerset.mp ha
    have hb' := mem_powerset.mp hb
    let w : ℕ → ℤ := fun i => (if i ∈ a then 1 else 0) - (if i ∈ b then 1 else 0)
    refine ⟨w, ?_, ?_⟩
    · intro i hi
      dsimp [w]
      split_ifs <;> norm_num
    · unfold signedSum
      have term (i : ℕ) : (w i : ℚ) / i =
          (if i ∈ a then 1 / (i : ℚ) else 0) -
          (if i ∈ b then 1 / (i : ℚ) else 0) := by
        dsimp [w]
        split_ifs <;> push_cast <;> ring
      simp_rw [term]
      rw [sum_sub_distrib]
      congr 1
      · rw [← sum_filter]
        congr 1
        rw [filter_mem_eq_inter, inter_eq_right.mpr ha']
      · rw [← sum_filter]
        congr 1
        rw [filter_mem_eq_inter, inter_eq_right.mpr hb']
  · rintro ⟨w, hw, rfl⟩
    let a := (Ico 1 m).filter (fun i => w i = 1)
    let b := (Ico 1 m).filter (fun i => w i = -1)
    have ha : (∑ i ∈ a, (1 : ℚ) / i) ∈ sumsBelow m :=
      mem_image.mpr ⟨a, mem_powerset.mpr (filter_subset _ _), rfl⟩
    have hb : (∑ i ∈ b, (1 : ℚ) / i) ∈ sumsBelow m :=
      mem_image.mpr ⟨b, mem_powerset.mpr (filter_subset _ _), rfl⟩
    apply mem_image.mpr
    refine ⟨(_, _), mem_product.mpr ⟨ha, hb⟩, ?_⟩
    change (∑ i ∈ a, (1 : ℚ) / i) - (∑ i ∈ b, (1 : ℚ) / i) = signedSum m w
    unfold a b signedSum
    rw [sum_filter, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have hwi := hw i hi
    have cases : w i = -1 ∨ w i = 0 ∨ w i = 1 := by omega
    rcases cases with hz | hz | hz <;> simp [hz, div_eq_mul_inv]

/-- A fully finite test for the signed-representation obstruction. -/
theorem irreducible_iff {m : ℕ} :
    Irreducible m ↔ 0 < m ∧ 1 / (m : ℚ) ∉ differences m := by
  simp only [Irreducible, mem_differences, not_exists, not_and]

/-- A fully finite test for a compatible prime, retaining reduced numerators. -/
theorem compatible_iff {m p : ℕ} :
    Compatible m p ↔ ∀ q ∈ differences m, ¬(p : ℤ) ∣ (1 / (m : ℚ) - q).num := by
  constructor
  · intro h q hq
    obtain ⟨w, hw, rfl⟩ := mem_differences.mp hq
    exact h w hw
  · intro h w hw
    exact h _ (mem_differences.mpr ⟨w, hw, rfl⟩)

/-- Adjoining denominator `m` adjoins one translate of the preceding set. -/
theorem sumsBelow_succ {m : ℕ} (hm : 0 < m) :
    sumsBelow (m + 1) = sumsBelow m ∪ (sumsBelow m).image (· + 1 / (m : ℚ)) := by
  unfold sumsBelow
  rw [Nat.Ico_succ_right_eq_insert_Ico hm, powerset_insert, image_union]
  simp only [image_image]
  congr 1
  apply image_congr
  intro a ha
  have hma : m ∉ a := fun h => Nat.lt_irrefl m (mem_Ico.mp (mem_powerset.mp ha h)).2
  simp [sum_insert hma, add_comm]

/-- BGMS Lemma 1: the signed obstruction is equivalent to exact doubling. -/
theorem irreducible_iff_doubling {m : ℕ} (hm : 0 < m) :
    Irreducible m ↔ (sumsBelow (m + 1)).card = 2 * (sumsBelow m).card := by
  rw [irreducible_iff, and_iff_right hm, sumsBelow_succ hm]
  have hcard : ((sumsBelow m).image (· + 1 / (m : ℚ))).card = (sumsBelow m).card :=
    card_image_of_injective _ (add_left_injective _)
  rw [two_mul]
  nth_rw 2 [← hcard]
  rw [card_union_eq_card_add_card]
  rw [disjoint_left]
  constructor
  · intro h x hx hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx'
    apply h
    exact mem_image.mpr ⟨(y + 1 / (m : ℚ), y), mem_product.mpr ⟨hx, hy⟩, by simp⟩
  · intro h hmem
    obtain ⟨⟨x,y⟩, hxy, hq⟩ := mem_image.mp hmem
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    apply h hx
    exact mem_image.mpr ⟨y, hy, by dsimp at hq; linarith⟩

/-- Every compatible prime power produces exact doubling of the original count. -/
theorem compatible_prime_doubling {m p k : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hc : Compatible m p) :
    (sumsBelow (m * p ^ k + 1)).card = 2 * (sumsBelow (m * p ^ k)).card :=
  (irreducible_iff_doubling (Nat.mul_pos hm (pow_pos hp.pos k))).mp
    (compatible_prime_extension hm hp hc)

/-- A computable cutoff; it is not the sharper harmonic-lcm cutoff in BGMS. -/
def numeratorBound (m : ℕ) : ℕ :=
  (differences m).sup (fun q => (1 / (m : ℚ) - q).num.natAbs)

/-- All primes above a finite numerator cutoff are compatible. -/
theorem compatible_of_large {m p : ℕ} (hm : Irreducible m)
    (hlarge : numeratorBound m < p) : Compatible m p := by
  apply compatible_iff.mpr
  intro q hq hdvd
  have hqne : 1 / (m : ℚ) - q ≠ 0 := by
    intro hzero
    have heq : q = 1 / (m : ℚ) := by linarith
    exact (irreducible_iff.mp hm).2 (heq ▸ hq)
  have hnum0 : 0 < (1 / (m : ℚ) - q).num.natAbs :=
    Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hqne)
  have hpdvd : p ∣ (1 / (m : ℚ) - q).num.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hle : p ≤ numeratorBound m :=
    (Nat.le_of_dvd hnum0 hpdvd).trans (Finset.le_sup (f := fun q => (1 / (m : ℚ) - q).num.natAbs) hq)
  omega

/-- Every irreducible seed has compatible primes exceeding any prescribed bound. -/
theorem exists_large_compatible_prime {m : ℕ} (hm : Irreducible m) (B : ℕ) :
    ∃ p, B < p ∧ p.Prime ∧ Compatible m p := by
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max B (numeratorBound m) + 1)
  refine ⟨p, by omega, hp, compatible_of_large hm ?_⟩
  have := le_max_right B (numeratorBound m)
  omega

/-- Arbitrarily large multiples of every irreducible seed are exact-doubling indices. -/
theorem exists_large_doubling_multiple {m : ℕ} (hm : Irreducible m) (B : ℕ) :
    ∃ n, B < n ∧ m ∣ n ∧ (sumsBelow (n + 1)).card = 2 * (sumsBelow n).card := by
  obtain ⟨p, hpB, hp, hc⟩ := exists_large_compatible_prime hm B
  refine ⟨m * p, ?_, dvd_mul_right m p, ?_⟩
  · have := hm.1
    nlinarith
  · simpa using compatible_prime_doubling (k := 1) hm.1 hp hc

/-- The seed one is compatible with every prime. -/
theorem one_compatible {p : ℕ} (hp : p.Prime) : Compatible 1 p := by
  intro w hw
  simp only [signedSum, Ico_self, sum_empty, Nat.cast_one, div_one, sub_zero, Rat.num_one]
  intro hd
  have hd' : p ∣ 1 := by simpa using Int.natAbs_dvd_natAbs.mpr hd
  exact hp.ne_one (Nat.dvd_one.mp hd')

/-- Every prime power is an exact-doubling index, including exponent zero. -/
theorem prime_power_doubling {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sumsBelow (p ^ k + 1)).card = 2 * (sumsBelow (p ^ k)).card := by
  simpa using compatible_prime_doubling (m := 1) (k := k) (by omega) hp (one_compatible hp)

/-- Executable irreducibility test. -/
def isIrreducible (m : ℕ) : Bool := decide (0 < m ∧ 1 / (m : ℚ) ∉ differences m)

/-- Executable compatibility test; primality is checked separately by clients. -/
def isCompatible (m p : ℕ) : Bool :=
  decide (∀ q ∈ differences m, ¬(p : ℤ) ∣ (1 / (m : ℚ) - q).num)

theorem isIrreducible_correct (m : ℕ) : isIrreducible m = true ↔ Irreducible m := by
  simp only [isIrreducible, decide_eq_true_eq, irreducible_iff]

theorem isCompatible_correct (m p : ℕ) : isCompatible m p = true ↔ Compatible m p := by
  simp only [isCompatible, decide_eq_true_eq, compatible_iff]

/-- This instance explicitly permits both `p ≤ m` and `p ∣ m`. -/
theorem four_two_compatible : Compatible 4 2 := by
  apply (isCompatible_correct 4 2).mp
  decide +kernel

/-- The BGMS example `4·23 = 92`, now certified for every exponent. -/
theorem four_twenty_three_compatible : Compatible 4 23 := by
  apply (isCompatible_correct 4 23).mp
  decide +kernel

theorem four_two_power_doubling (k : ℕ) :
    (sumsBelow (4 * 2 ^ k + 1)).card = 2 * (sumsBelow (4 * 2 ^ k)).card :=
  compatible_prime_doubling (by norm_num) (by norm_num) four_two_compatible

theorem four_twenty_three_power_doubling (k : ℕ) :
    (sumsBelow (4 * 23 ^ k + 1)).card = 2 * (sumsBelow (4 * 23 ^ k)).card :=
  compatible_prime_doubling (by norm_num) (by norm_num) four_twenty_three_compatible

theorem four_numeratorBound : numeratorBound 4 = 25 := by decide +kernel

/-- Compatibility is a real restriction: the prime 3 cannot extend the seed 4. -/
theorem four_three_not_compatible : ¬Compatible 4 3 := by
  intro h
  have := (isCompatible_correct 4 3).mpr h
  have hn : isCompatible 4 3 = false := by decide +kernel
  rw [hn] at this
  contradiction

/-- The exact counting function for denominators `1,...,N`. -/
def S (N : ℕ) : ℕ := (sumsBelow (N + 1)).card

/-- Irreducible indices up to `N`, computed by the finite obstruction test. -/
def doublingIndices (N : ℕ) : Finset ℕ :=
  (Ico 1 (N + 1)).filter (fun m => isIrreducible m = true)

theorem sumsBelow_subset_succ {m : ℕ} (hm : 0 < m) :
    sumsBelow m ⊆ sumsBelow (m + 1) := by
  rw [sumsBelow_succ hm]
  exact subset_union_left

/-- BGMS Lemma 2, as an exact finite lower bound rather than an asymptotic statement. -/
theorem doubling_count_lower_bound (N : ℕ) : 2 ^ (doublingIndices N).card ≤ S N := by
  induction N with
  | zero => norm_num [doublingIndices, S, sumsBelow]
  | succ N ih =>
    have hpos : 0 < N + 1 := by omega
    have hnot : N + 1 ∉ doublingIndices N := by simp [doublingIndices]
    have hstep : doublingIndices (N + 1) =
        if isIrreducible (N + 1) = true then insert (N + 1) (doublingIndices N)
        else doublingIndices N := by
      unfold doublingIndices
      rw [Nat.Ico_succ_right_eq_insert_Ico hpos, filter_insert]
    rw [hstep]
    by_cases h : isIrreducible (N + 1) = true
    · rw [ite_eq_left h, card_insert_of_notMem hnot, pow_succ]
      have hd := (irreducible_iff_doubling hpos).mp ((isIrreducible_correct _).mp h)
      change 2 ^ (doublingIndices N).card * 2 ≤ (sumsBelow (N + 1 + 1)).card
      rw [hd]
      change 2 ^ (doublingIndices N).card * 2 ≤ 2 * S N
      omega
    · rw [ite_eq_right h]
      exact ih.trans (card_le_card (sumsBelow_subset_succ hpos))

end ReciprocalDoubling
