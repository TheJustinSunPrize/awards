import Mathlib

/-!
# Erdős Problem 670: separated distances on the line force diameter `(1 + o(1)) n²`

Erdős Problem 670 (<https://www.erdosproblems.com/670>, from [Er97f, p. 6]) asks:

> Let `A ⊆ ℝ^d` be a set of `n` points such that all pairwise distances differ by at least `1`.
> Is the diameter of `A` at least `(1 + o(1)) n²`?

The problem is open in general (for fixed `d ≥ 2`). The site records that the trivial lower
bound is `n choose 2`, and that Erdős [Er97f] proved the claim when `d = 1`. This file proves
that one-dimensional case.

Google DeepMind's formal-conjectures project has no file for Problem 670 (checked against a local
copy of `FormalConjectures/ErdosProblems/`), so the definitions below are made directly from the
problem statement: `DistancesSeparated A` says that the distances of any
two different unordered pairs of distinct points of `A` differ by at least `1`, and
`Erdos670Statement d` is the fixed-dimension reading of the question in `EuclideanSpace ℝ (Fin d)`
(for every `n` and every such `A` with `n` points, `diam A ≥ (1 + f n) n²` for some `f → 0`).

## Main results

* `mul_sub_one_le_diam`: explicit bound. If `A ⊆ ℝ` is separated, `n = #A` and `k ≤ n`, then
  with `m = k n - k (k + 1) / 2` we have `m (m - 1) ≤ k (k + 1) · diam A`.
* `erdos_670_real_eps`: for every `ε > 0` and all large `n`, `diam A ≥ (1 - ε) n²`.
* `erdos_670_real`: the `(1 + o(1)) n²` form over `ℝ`.
* `erdos_670_dim_one : Erdos670Statement 1`: the same statement in `EuclideanSpace ℝ (Fin 1)`.
* `exists_distancesSeparated`: for every `n` there is a separated `n`-point set in `ℝ`
  (`{2⁰, …, 2ⁿ⁻¹}`), so the hypotheses are satisfiable.

## Proof

Sort `A` as `x₀ < x₁ < ⋯ < x_{n-1}` and fix `k ≤ n`. The index pairs `(i, i + s)` with
`1 ≤ s ≤ k` number `m = ∑_{s=1}^{k} (n - s) = k n - k (k + 1) / 2`. Their distances
`x_{i+s} - x_i` are nonnegative and pairwise `1`-separated, so they sum to at least `m (m - 1) / 2`.
On the other hand, for each `s` the sum `∑_i (x_{i+s} - x_i)` telescopes into `s` sums
`∑_i (x_{i+t+1} - x_{i+t}) ≤ x_{n-1} - x₀ ≤ diam A`, so the total is at most
`k (k + 1) / 2 · diam A`. Taking `k` a large constant (`k = ⌈2 / ε⌉`) gives
`diam A ≥ (1 - ε) n²` for `n ≥ (k + 1)² + 1`.

## References

- [Er97f] Erdős, Paul. Some unsolved problems. Combinatorics, geometry and probability
  (Cambridge, 1993), Cambridge Univ. Press, 1997, 1–10.
- [Ho26] Ho, Boon Suan. Erdős's diameter conjecture for separated distances fails in high
  dimensions. arXiv:2604.15305 (2026).
-/

open Finset Filter Topology

open scoped Finset

namespace Erdos670

/-- All pairwise distances of the finite point set `A` differ by at least `1`: whenever
`{a, b}` and `{c, e}` are two different unordered pairs of distinct points of `A`,
`|dist a b - dist c e| ≥ 1`. -/
def DistancesSeparated {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/-- Erdős Problem 670 in fixed dimension `d`: there is `f : ℕ → ℝ` with `f n → 0` such that every
set `A ⊆ ℝ^d` of `n` points whose pairwise distances differ by at least `1` has
`diam A ≥ (1 + f n) n²`. Erdős proved this for `d = 1` (`erdos_670_dim_one`); it is open for
`d ≥ 2`. -/
def Erdos670Statement (d : ℕ) : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin d)), #A = n → DistancesSeparated A →
      (1 + f n) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d)))

/-! ### A sum of `1`-separated nonnegative reals -/

/-- `m` nonnegative reals that are pairwise at distance at least `1` sum to at least
`m (m - 1) / 2`; moreover one of them is at least `m - 1`. -/
theorem sum_ge_of_one_separated (S : Finset ℝ) (h0 : ∀ x ∈ S, 0 ≤ x)
    (h1 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (#S : ℝ) * (#S - 1) / 2 ≤ ∑ x ∈ S, x ∧ (S.Nonempty → ∃ x ∈ S, (#S : ℝ) - 1 ≤ x) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    obtain ⟨ihs, ihm⟩ := ih (fun x hx => h0 x (mem_insert_of_mem hx))
      (fun x hx y hy => h1 x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
    have hca : (#S : ℝ) ≤ a := by
      rcases S.eq_empty_or_nonempty with hS | hS
      · simp [hS, h0 a (mem_insert_self a S)]
      · obtain ⟨x, hx, hxc⟩ := ihm hS
        have hxa := ha x hx
        have := h1 a (mem_insert_self a S) x (mem_insert_of_mem hx) (ne_of_gt hxa)
        rw [abs_of_pos (sub_pos.2 hxa)] at this
        linarith
    rw [card_insert_of_notMem haS, sum_insert haS]
    push_cast
    exact ⟨by nlinarith, fun _ => ⟨a, mem_insert_self a S, by linarith⟩⟩

/-! ### The abstract inequality for a sorted sequence -/

/-- Telescoping: for a sequence nondecreasing on `[0, n)` and `L + j ≤ n`,
`∑_{i < L} (x (i + j) - x i) ≤ j (x (n - 1) - x 0)`. -/
theorem sum_sub_le (x : ℕ → ℝ) (n : ℕ) (hmono : ∀ i j, i ≤ j → j < n → x i ≤ x j)
    (L j : ℕ) (hLj : L + j ≤ n) :
    ∑ i ∈ range L, (x (i + j) - x i) ≤ j * (x (n - 1) - x 0) := by
  have h1 : ∀ i, x (i + j) - x i = ∑ t ∈ range j, (x (i + t + 1) - x (i + t)) := by
    intro i
    have := sum_range_sub (fun t => x (i + t)) j
    simp only [add_zero] at this
    rw [← this]
    rfl
  have h2 : ∀ t ∈ range j, ∑ i ∈ range L, (x (i + t + 1) - x (i + t)) ≤ x (n - 1) - x 0 := by
    intro t ht
    rw [mem_range] at ht
    have htel := sum_range_sub (fun i => x (i + t)) L
    simp only [zero_add] at htel
    have hrw : ∑ i ∈ range L, (x (i + t + 1) - x (i + t)) = x (L + t) - x t := by
      rw [← htel]
      exact sum_congr rfl fun i _ => by rw [add_right_comm]
    rw [hrw]
    have ha : x 0 ≤ x t := hmono 0 t (Nat.zero_le _) (by omega)
    have hb : x (L + t) ≤ x (n - 1) := hmono _ _ (by omega) (by omega)
    linarith
  calc ∑ i ∈ range L, (x (i + j) - x i)
      = ∑ i ∈ range L, ∑ t ∈ range j, (x (i + t + 1) - x (i + t)) :=
        sum_congr rfl fun i _ => h1 i
    _ = ∑ t ∈ range j, ∑ i ∈ range L, (x (i + t + 1) - x (i + t)) := sum_comm
    _ ≤ ∑ t ∈ range j, (x (n - 1) - x 0) := sum_le_sum h2
    _ = j * (x (n - 1) - x 0) := by simp [mul_sub]

theorem sum_range_add_one (k : ℕ) : ∑ s ∈ range k, ((s : ℝ) + 1) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The key inequality for a sequence `x` that is nondecreasing on `[0, n)` and whose gaps
`x j - x i` (`i < j < n`) are pairwise `1`-separated: for `k ≤ n`, with
`m = k n - k (k + 1) / 2`, `m (m - 1) ≤ k (k + 1) (x (n - 1) - x 0)`. -/
theorem index_bound (x : ℕ → ℝ) (n : ℕ) (hmono : ∀ i j, i ≤ j → j < n → x i ≤ x j)
    (hsep : ∀ i j p q, i < j → j < n → p < q → q < n → (i ≠ p ∨ j ≠ q) →
      1 ≤ |(x j - x i) - (x q - x p)|)
    (k : ℕ) (hk : k ≤ n) :
    ((k : ℝ) * n - k * (k + 1) / 2) * ((k : ℝ) * n - k * (k + 1) / 2 - 1) ≤
      k * (k + 1) * (x (n - 1) - x 0) := by
  set P : Finset (Σ _ : ℕ, ℕ) := (range k).sigma fun s => range (n - (s + 1)) with hP
  set g : (Σ _ : ℕ, ℕ) → ℝ := fun p => x (p.2 + (p.1 + 1)) - x p.2 with hg
  have hmemP : ∀ p ∈ P, p.1 < k ∧ p.2 + (p.1 + 1) < n := by
    rintro ⟨s, i⟩ hp
    simp only [hP, mem_sigma, mem_range] at hp
    exact ⟨hp.1, by simp only; omega⟩
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    have := hmono p.2 (p.2 + (p.1 + 1)) (by omega) (hmemP p hp).2
    simp only [hg]
    linarith
  have hgsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ |g p - g q| := by
    rintro ⟨s, i⟩ hp ⟨t, j⟩ hq hpq
    have hp' := hmemP _ hp
    have hq' := hmemP _ hq
    simp only at hp' hq'
    apply hsep i (i + (s + 1)) j (j + (t + 1)) (by omega) hp'.2 (by omega) hq'.2
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, h2⟩ := h
    have hst : s = t := by omega
    subst hst
    exact hpq rfl
  have hinj : Set.InjOn g P := by
    intro p hp q hq hpq
    by_contra hne
    have := hgsep p hp q hq hne
    rw [hpq, sub_self, abs_zero] at this
    norm_num at this
  have hPcard : (#P : ℝ) = k * n - k * (k + 1) / 2 := by
    rw [hP, card_sigma, Nat.cast_sum]
    have : ∑ s ∈ range k, ((#(range (n - (s + 1))) : ℕ) : ℝ) =
        ∑ s ∈ range k, ((n : ℝ) - ((s : ℝ) + 1)) := by
      refine sum_congr rfl fun s hs => ?_
      rw [mem_range] at hs
      rw [card_range, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this, sum_sub_distrib, sum_range_add_one]
    simp
  have hlow := (sum_ge_of_one_separated (P.image g)
    (by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hv
      exact hg0 p hp)
    (by
      intro v hv w hw hvw
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hv
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hw
      exact hgsep p hp q hq fun h => hvw (h ▸ rfl))).1
  rw [card_image_of_injOn hinj, sum_image hinj, hPcard] at hlow
  have hup : ∑ p ∈ P, g p ≤ k * (k + 1) / 2 * (x (n - 1) - x 0) := by
    rw [hP, sum_sigma]
    calc ∑ s ∈ range k, ∑ i ∈ range (n - (s + 1)), g ⟨s, i⟩
        ≤ ∑ s ∈ range k, ((s : ℝ) + 1) * (x (n - 1) - x 0) := by
          apply sum_le_sum
          intro s hs
          rw [mem_range] at hs
          have := sum_sub_le x n hmono (n - (s + 1)) (s + 1) (by omega)
          push_cast at this
          exact this
      _ = k * (k + 1) / 2 * (x (n - 1) - x 0) := by rw [← sum_mul, sum_range_add_one]
  linarith

/-! ### The explicit bound for finite subsets of `ℝ` -/

/-- **Explicit form of Erdős's bound.** If the pairwise distances of `A ⊆ ℝ` differ by at least `1`
and `k ≤ #A`, then with `m = k · #A - k (k + 1) / 2`, `m (m - 1) ≤ k (k + 1) · diam A`. -/
theorem mul_sub_one_le_diam (A : Finset ℝ) (hA : DistancesSeparated A) (k : ℕ) (hk : k ≤ #A) :
    ((k : ℝ) * #A - k * (k + 1) / 2) * ((k : ℝ) * #A - k * (k + 1) / 2 - 1) ≤
      k * (k + 1) * Metric.diam (A : Set ℝ) := by
  set n := #A with hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hk0 : k = 0 := by omega
    subst hk0
    simp
  set e := A.orderEmbOfFin hn.symm with he
  let x : ℕ → ℝ := fun i => if h : i < n then e ⟨i, h⟩ else 0
  have hx : ∀ i (h : i < n), x i = e ⟨i, h⟩ := fun i h => by simp [x, h]
  have hxmem : ∀ i, i < n → x i ∈ A := fun i h => by
    rw [hx i h]
    exact A.orderEmbOfFin_mem _ _
  have hmono : ∀ i j, i ≤ j → j < n → x i ≤ x j := by
    intro i j hij hj
    rw [hx i (by omega), hx j hj]
    exact e.monotone (Fin.mk_le_mk.2 hij)
  have hsmono : ∀ i j, i < j → j < n → x i < x j := by
    intro i j hij hj
    rw [hx i (by omega), hx j hj]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  have hxinj : ∀ i j, i < n → j < n → x i = x j → i = j := by
    intro i j hi hj h
    rw [hx i hi, hx j hj] at h
    exact Fin.mk.inj_iff.1 (e.injective h)
  have hdist : ∀ i j, i < j → j < n → dist (x i) (x j) = x j - x i := by
    intro i j hij hj
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hsmono i j hij hj).le)]
  have hsep : ∀ i j p q, i < j → j < n → p < q → q < n → (i ≠ p ∨ j ≠ q) →
      1 ≤ |(x j - x i) - (x q - x p)| := by
    intro i j p q hij hj hpq hq hne
    rw [← hdist i j hij hj, ← hdist p q hpq hq]
    refine hA _ (hxmem i (by omega)) _ (hxmem j hj) _ (hxmem p (by omega)) _ (hxmem q hq)
      (hsmono i j hij hj).ne (hsmono p q hpq hq).ne ?_
    intro hs
    rcases Sym2.eq_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hxinj i p (by omega) (by omega) h1
      have := hxinj j q hj hq h2
      omega
    · have := hxinj i q (by omega) hq h1
      have := hxinj j p hj (by omega) h2
      omega
  have hD : x (n - 1) - x 0 ≤ Metric.diam (A : Set ℝ) := by
    have := Metric.dist_le_diam_of_mem A.finite_toSet.isBounded
      (hxmem (n - 1) (by omega)) (hxmem 0 hpos)
    rw [Real.dist_eq] at this
    exact (le_abs_self _).trans this
  have hk0 : (0 : ℝ) ≤ k * (k + 1) := by positivity
  calc _ ≤ k * (k + 1) * (x (n - 1) - x 0) := index_bound x n hmono hsep k hk
    _ ≤ _ := mul_le_mul_of_nonneg_left hD hk0

/-! ### Asymptotic forms -/

/-- **Erdős [Er97f], `d = 1`, `ε`-form.** For every `ε > 0` there is `N` such that every set of
`n ≥ N` reals whose pairwise distances differ by at least `1` has diameter at least
`(1 - ε) n²`. -/
theorem erdos_670_real_eps :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℝ, #A = n → DistancesSeparated A →
      (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set ℝ) := by
  intro ε hε
  set k := ⌈2 / ε⌉₊ with hk
  refine ⟨(k + 1) ^ 2 + 1, fun n hn A hA hsep => ?_⟩
  have hkε : 2 / ε ≤ k := Nat.le_ceil _
  have hk1 : 0 < k := Nat.lt_ceil.2 (by simpa using div_pos two_pos hε)
  have hkn : k ≤ n := by
    have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    omega
  have hb := mul_sub_one_le_diam A hsep k (hA ▸ hkn)
  rw [hA] at hb
  set D := Metric.diam (A : Set ℝ) with hD
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hnR : ((k : ℝ) + 1) ^ 2 + 1 ≤ n := by exact_mod_cast hn
  have hεk : 2 ≤ ε * (k + 1) := by
    rw [div_le_iff₀ hε] at hkε
    nlinarith
  set a : ℝ := n - (k + 1) / 2 with ha
  have hm : (k : ℝ) * n - k * (k + 1) / 2 = k * a := by rw [ha]; ring
  rw [hm] at hb
  have hkpos : (0 : ℝ) < k := by linarith
  have hb' : a * (k * a - 1) ≤ (k + 1) * D := by
    have h' : (k : ℝ) * (a * (k * a - 1)) ≤ k * ((k + 1) * D) := by linarith
    exact le_of_mul_le_mul_left h' hkpos
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hc : (0 : ℝ) < k + 1 := by positivity
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have han : a ≤ n := by rw [ha]; linarith
  have h1 : a ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ ha0 han 2
  have h2 : ((k : ℝ) + 1) * ((n : ℝ) ^ 2 - (k + 1) * n) ≤ (k + 1) * a ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [ha]
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have h3 : 2 * (n : ℝ) ^ 2 ≤ ε * (k + 1) * n ^ 2 :=
    mul_le_mul_of_nonneg_right hεk (by positivity)
  have h4 : ((k : ℝ) + 1) ^ 2 * n + n ≤ n ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hnR hn0]
  have h5 : (1 - ε) * n ^ 2 * (k + 1) ≤ D * (k + 1) := by nlinarith
  exact le_of_mul_le_mul_right h5 hc

/-- **Erdős [Er97f], `d = 1`.** The `(1 + o(1)) n²` form over `ℝ`: there is `f → 0` such that every
`n`-point set of reals with pairwise distances differing by at least `1` has diameter at least
`(1 + f n) n²`. -/
theorem erdos_670_real :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ A : Finset ℝ, #A = n → DistancesSeparated A →
        (1 + f n) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set ℝ) := by
  let S : ℕ → Set ℝ := fun n =>
    {r | ∃ A : Finset ℝ, #A = n ∧ DistancesSeparated A ∧
      r = Metric.diam (A : Set ℝ) / (n : ℝ) ^ 2 - 1}
  refine ⟨fun n => min 0 (sInf (S n)), ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := erdos_670_real_eps (ε / 2) (by positivity)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hnN : N ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hlow : -(ε / 2) ≤ sInf (S n) := by
      rcases (S n).eq_empty_or_nonempty with h | h
      · rw [h, Real.sInf_empty]
        linarith
      · apply le_csInf h
        rintro r ⟨A, hA, hsep, rfl⟩
        have := hN n hnN A hA hsep
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        rw [le_sub_iff_add_le, le_div_iff₀ hn2]
        linarith
    have hmin : -(ε / 2) ≤ min 0 (sInf (S n)) := le_min (by linarith) hlow
    rw [Real.dist_eq, sub_zero, abs_of_nonpos (min_le_left _ _)]
    linarith
  · intro n A hA hsep
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Metric.diam_nonneg
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hbdd : BddBelow (S n) := ⟨-1, by
      rintro r ⟨B, -, -, rfl⟩
      have := div_nonneg (Metric.diam_nonneg (s := (B : Set ℝ))) hn2.le
      linarith⟩
    have hmem : Metric.diam (A : Set ℝ) / (n : ℝ) ^ 2 - 1 ∈ S n := ⟨A, hA, hsep, rfl⟩
    have h1 : min 0 (sInf (S n)) ≤ Metric.diam (A : Set ℝ) / (n : ℝ) ^ 2 - 1 :=
      (min_le_right _ _).trans (csInf_le hbdd hmem)
    have h2 : (1 + min 0 (sInf (S n))) * (n : ℝ) ^ 2 ≤
        (Metric.diam (A : Set ℝ) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hn2.le
    rwa [div_mul_cancel₀ _ hn2.ne'] at h2

/-! ### Transfer to `EuclideanSpace ℝ (Fin 1)` -/

theorem DistancesSeparated.image_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [DecidableEq Y] {f : X → Y} (hf : Isometry f) {A : Finset X} (hA : DistancesSeparated A) :
    DistancesSeparated (A.image f) := by
  intro a ha b hb c hc e he hab hce hs
  obtain ⟨a', ha', rfl⟩ := mem_image.1 ha
  obtain ⟨b', hb', rfl⟩ := mem_image.1 hb
  obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
  obtain ⟨e', he', rfl⟩ := mem_image.1 he
  rw [hf.dist_eq, hf.dist_eq]
  exact hA a' ha' b' hb' c' hc' e' he' (fun h => hab (h ▸ rfl)) (fun h => hce (h ▸ rfl))
    (fun h => hs (by simpa using congrArg (Sym2.map f) h))

/-- The coordinate map `EuclideanSpace ℝ (Fin 1) → ℝ` is an isometry. -/
theorem isometry_coord : Isometry fun x : EuclideanSpace ℝ (Fin 1) => x 0 := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg]

/-- **Erdős Problem 670 for `d = 1` (Erdős [Er97f]).** -/
theorem erdos_670_dim_one : Erdos670Statement 1 := by
  obtain ⟨f, hf, hbound⟩ := erdos_670_real
  refine ⟨f, hf, fun n A hA hsep => ?_⟩
  have h := hbound n (A.image fun x => x 0)
    (by rw [card_image_of_injective _ isometry_coord.injective, hA])
    (hsep.image_isometry isometry_coord)
  rwa [coe_image, isometry_coord.diam_image] at h

/-! ### Non-vacuity -/

theorem two_pow_sub_inj {i j p q : ℕ} (hij : i < j) (hpq : p < q)
    (h : 2 ^ j - 2 ^ i = 2 ^ q - 2 ^ p) : i = p ∧ j = q := by
  have key : ∀ i j q p : ℕ, i < j → p < q → j < q → 2 ^ j - 2 ^ i < 2 ^ q - 2 ^ p := by
    intro i j q p hij hpq hjq
    have h1 : 2 ^ j ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right two_pos (by omega)
    have h2 : 2 ^ p ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right two_pos (by omega)
    have h3 : 2 ^ q = 2 * 2 ^ (q - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h4 : 0 < 2 ^ i := by positivity
    have h5 : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right two_pos hij.le
    omega
  have hjq : j = q := by
    rcases lt_trichotomy j q with hjq | hjq | hjq
    · exact absurd h (key i j q p hij hpq hjq).ne
    · exact hjq
    · exact absurd h (key p q j i hpq hij hjq).ne'
  subst hjq
  refine ⟨Nat.pow_right_injective le_rfl ?_, rfl⟩
  have h5 : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right two_pos hij.le
  have h6 : 2 ^ p ≤ 2 ^ j := Nat.pow_le_pow_right two_pos hpq.le
  simp only
  omega

/-- The hypothesis is satisfiable for every `n`: the distances of `{2⁰, 2¹, …, 2ⁿ⁻¹}` are
distinct integers. -/
theorem exists_distancesSeparated (n : ℕ) : ∃ A : Finset ℝ, #A = n ∧ DistancesSeparated A := by
  have hinj : Function.Injective fun i : ℕ => (2 : ℝ) ^ i :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective
  refine ⟨(range n).image fun i => (2 : ℝ) ^ i, by rw [card_image_of_injective _ hinj, card_range],
    ?_⟩
  have hd : ∀ i j : ℕ, dist ((2 : ℝ) ^ i) (2 ^ j) = ((2 ^ max i j - 2 ^ min i j : ℕ) : ℝ) := by
    intro i j
    rcases le_total i j with h | h
    · rw [max_eq_right h, min_eq_left h, Nat.cast_sub (Nat.pow_le_pow_right two_pos h),
        Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (pow_le_pow_right₀ one_le_two h))]
      push_cast
      ring
    · rw [max_eq_left h, min_eq_right h, Nat.cast_sub (Nat.pow_le_pow_right two_pos h),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (pow_le_pow_right₀ one_le_two h))]
      push_cast
      ring
  intro a ha b hb c hc e he hab hce hs
  obtain ⟨i, -, rfl⟩ := mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := mem_image.1 hb
  obtain ⟨p, -, rfl⟩ := mem_image.1 hc
  obtain ⟨q, -, rfl⟩ := mem_image.1 he
  rw [hd, hd]
  have hij : i ≠ j := fun h => hab (h ▸ rfl)
  have hpq : p ≠ q := fun h => hce (h ▸ rfl)
  have hne : (2 ^ max i j - 2 ^ min i j : ℕ) ≠ 2 ^ max p q - 2 ^ min p q := by
    intro h
    obtain ⟨h1, h2⟩ := two_pow_sub_inj (by omega) (by omega) h
    have hs' : s(i, j) = s(p, q) := Sym2.eq_iff.2 (by omega)
    exact hs (by simpa using congrArg (Sym2.map fun i : ℕ => (2 : ℝ) ^ i) hs')
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : ((2 ^ max i j - 2 ^ min i j : ℕ) : ℝ) + 1 ≤ ((2 ^ max p q - 2 ^ min p q : ℕ) : ℝ) := by
      exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : ((2 ^ max p q - 2 ^ min p q : ℕ) : ℝ) + 1 ≤ ((2 ^ max i j - 2 ^ min i j : ℕ) : ℝ) := by
      exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith

end Erdos670
