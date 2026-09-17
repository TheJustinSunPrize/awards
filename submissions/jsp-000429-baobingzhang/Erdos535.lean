import Mathlib

/-!
# Erdős Problem 535: Erdős's lower bound `f_r(N) > N^(c / log log N)`

Erdős Problem 535 ([Er64], https://www.erdosproblems.com/535) reads:

> Let `r ≥ 3`, and let `f_r(N)` denote the size of the largest subset of `{1, …, N}` such that
> no subset of size `r` has the same pairwise greatest common divisor between all elements.
> Estimate `f_r(N)`.

The problem is open. Erdős [Er64] proved that for every `r ≥ 3` there is `c_r > 0` with
`f_r(N) > N^(c_r / log log N)`, and conjectured that this is also the right upper bound. This file
proves that lower bound for every `r ≥ 3` (with the single constant `c = 1/16`). The r = 3 case is
stated without proof as `erdos_535.variants.lower_bound` (category "research solved") in Google
DeepMind's formal-conjectures project, `FormalConjectures/ErdosProblems/535.lean`.

## Definitions and faithfulness

* `Erdos535.f` and the statement of `erdos_535.variants.lower_bound` (with its docstring) are
  copied verbatim from `FormalConjectures/ErdosProblems/535.lean` (Apache-2.0). That file opens
  `ArithmeticFunction`, `Filter`, `Real` and some scoped notation; here only `Filter` and `Real` are
  opened. The statement elaborates to the same term either way: `log` is `Real.log`.
* `f r N` is `sSup` of the sizes of all `A ⊆ {1, …, N}` in which no `r`-element subset `S` has a
  common value `d` of `gcd a b` for all distinct `a, b ∈ S`. This is the definition on the
  problem page. `NoEqualGcd r A` names the condition (`f_eq` is `rfl`).
* `f` is a genuine maximum, not a junk value of `sSup`: the defining set is bounded by `N`
  (`bddAbove_setOf`, `f_le`), and for `r ≥ 1` it contains `0` (the empty set) and so its supremum
  is attained (`exists_card_eq_f`). Hence `N^(c / log log N) ≤ f 3 N` really says that some
  admissible `A ⊆ {1, …, N}` has at least that many elements.
* The bound `N^(c / log log N) = exp (c log N / log log N)` tends to infinity, so the statement is
  not implied by any bounded lower bound on `f`.

## Proof

* **Construction** (`blockProd`, `noEqualGcd_three`). Let `p_k` be the `k`-th prime and group
  the first `2m` primes into the pairs `{p_{2i}, p_{2i+1}}`, `i < m`. For `T ⊆ {0, …, m-1}` put
  `a_T = ∏_{i<m} p_{2i + [i ∈ T]}` (one prime from each pair). The prime `p_k` divides `a_T` iff
  `k = 2i + [i ∈ T]` for some `i < m` (`nth_dvd_blockProd_iff`), so `T ↦ a_T` is injective
  (`blockProd_injOn`) and the `2^m` numbers `a_T` contain no three with equal pairwise gcd:
  if `a_T, a_U, a_V` are distinct, pick `i` with `i ∈ T` and `i ∉ U` or vice versa; two of the
  three sets agree at `i`, say they choose the prime `q` of pair `i` while the third one does not.
  Then `q` divides the gcd of the first two but not a gcd involving the third, so the three
  pairwise gcds are not all equal.
* **Size** (`blockProd_dvd_primorial`, `two_pow_le_f`). If `2m ≤ π(y)` then every `a_T` divides
  the primorial `y#`, which is at most `4^y` (Mathlib). So `4^y ≤ N` gives
  `f 3 N ≥ 2^⌊π(y)/2⌋`.
* **Chebyshev** (`primeCounting_mul_log_ge`). Mathlib's `Chebyshev.psi_ge` and
  `Chebyshev.psi_le_primeCounting_mul_log` give `y log 2 - log (y + 1) ≤ π(y) log y`.
* **Asymptotics** (`main_bound`). Let `L = log N ≥ 512`, `y = ⌊L / log 4⌋` and `m = ⌊π(y)/2⌋`.
  Then `4^y ≤ N`, `1 ≤ y`, `y + 1 ≤ L`, `log L ≤ L / 16` and Chebyshev give
  `m log L > L / 8`, hence `(1/16) L / log L < m log 2`, i.e.
  `N^((1/16) / log log N) < 2^m ≤ f 3 N`.
* **All `r ≥ 3`** (`f_mono`). A set with no three elements of equal pairwise gcd has no `r` such
  elements for any `r ≥ 3`, so `f 3 N ≤ f r N`.

The block construction is the classical one; the bookkeeping (pairs of primes, the primorial
bound, Mathlib's Chebyshev estimates, the explicit constant `1/16`) is chosen for this
formalization and may differ from [Er64].

## Main results

* `Erdos535.erdos_535.variants.lower_bound : ∃ c > (0 : ℝ), ∀ᶠ (N : ℕ) in atTop,
    (N : ℝ) ^ (c / log (log (N : ℝ))) ≤ (f 3 N : ℝ)` (the formal-conjectures statement).
* `Erdos535.erdos_535.variants.lower_bound_of_three_le : 3 ≤ r → ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (c / log (log (N : ℝ))) < (f r N : ℝ)` (every `r ≥ 3`, strict
  inequality as on the problem page).
* `Erdos535.exists_card_eq_f`, `Erdos535.f_le`: `f r N` is an attained maximum and `f r N ≤ N`.

## What is not proved here

* The problem itself (the true order of `f_r(N)`), which is open, and the conjectured upper bound
  `f_r(N) ≤ N^(C_r / log log N)`.
* The known upper bounds: Erdős's `N^(3/4 + o(1))` [Er64], Abbott–Hanson's `N^(1/2 + o(1))`
  [AbHa70], and the bound `N^(C_r log log log N / log log N)` from the sunflower bounds of
  Alweiss–Lovett–Wu–Zhang [ALWZ20].
* Any dependence of the constant on `r`: a single constant `c = 1/16` is used for all `r ≥ 3`.

## References

* [Er64] Erdős, P., _On a problem in elementary number theory and a combinatorial problem_.
  Math. Comp. 18 (1964), 644-646.
* [AbHa70] Abbott, H. L. and Hanson, D., _An extremal problem in number theory_. Bull. London
  Math. Soc. 2 (1970), 324-326.
* [ALWZ20] Alweiss, R., Lovett, S., Wu, K. and Zhang, J., _Improved bounds for the sunflower
  lemma_ (2020).
* [erdosproblems.com/535](https://www.erdosproblems.com/535)
* Google DeepMind, formal-conjectures, `FormalConjectures/ErdosProblems/535.lean` (Apache-2.0).
-/

open Filter Real

namespace Erdos535

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

/-- The condition in the definition of `f`: no `r` elements of `A` have the same pairwise gcd. -/
def NoEqualGcd (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r → ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)

/-- `f` unfolded with the name `NoEqualGcd` for its condition. -/
theorem f_eq (r N : ℕ) :
    f r N = sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoEqualGcd r A ∧ A.card = k} :=
  rfl

/-- The set defining `f r N` is bounded by `N`. -/
theorem bddAbove_setOf (r N : ℕ) :
    BddAbove {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoEqualGcd r A ∧ A.card = k} := by
  refine ⟨N, ?_⟩
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- `f r N` is attained: some admissible `A ⊆ {1,…,N}` has exactly `f r N` elements. -/
theorem exists_card_eq_f {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoEqualGcd r A ∧ A.card = f r N := by
  have h0 : NoEqualGcd r ∅ := by
    intro S hS hcard
    rw [Finset.subset_empty.1 hS, Finset.card_empty] at hcard
    omega
  exact Nat.sSup_mem
    (s := {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoEqualGcd r A ∧ A.card = k})
    ⟨0, ∅, Finset.empty_subset _, h0, rfl⟩ (bddAbove_setOf r N)

/-- Every admissible `A ⊆ {1, …, N}` has at most `f r N` elements. -/
theorem card_le_f {r N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (h : NoEqualGcd r A) :
    A.card ≤ f r N :=
  le_csSup (bddAbove_setOf r N) ⟨A, hA, h, rfl⟩

/-- `f r N ≤ N`. -/
theorem f_le (r N : ℕ) : f r N ≤ N := by
  refine csSup_le' ?_
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- The condition for `r` implies the condition for every `s ≥ r`. -/
theorem NoEqualGcd.mono {r s : ℕ} {A : Finset ℕ} (h : NoEqualGcd r A) (hrs : r ≤ s) :
    NoEqualGcd s A := by
  rintro S hS hcard ⟨d, hd⟩
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hrs : r ≤ S.card)
  exact h T (hTS.trans hS) hT ⟨d, hd.mono (by simpa using hTS)⟩

/-- `f r N` is monotone in `r ≥ 1`. -/
theorem f_mono {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (N : ℕ) : f r N ≤ f s N := by
  obtain ⟨A, hA, h, hcard⟩ := exists_card_eq_f hr N
  exact hcard ▸ card_le_f hA (h.mono hrs)

/-! ### The construction -/

/-- `blockProd m T = ∏_{i < m} p_{2i + [i ∈ T]}`, where `p_k = Nat.nth Nat.Prime k` is the
`k`-th prime (`p_0 = 2`). -/
noncomputable def blockProd (m : ℕ) (T : Finset ℕ) : ℕ :=
  ∏ i ∈ Finset.range m, Nat.nth Nat.Prime (2 * i + if i ∈ T then 1 else 0)

/-- The prime `p_k` divides `blockProd m T` iff `k = 2i + [i ∈ T]` for some `i < m`. -/
theorem nth_dvd_blockProd_iff {m k : ℕ} {T : Finset ℕ} :
    Nat.nth Nat.Prime k ∣ blockProd m T ↔ ∃ i < m, k = 2 * i + if i ∈ T then 1 else 0 := by
  constructor
  · intro h
    obtain ⟨i, hi, hdvd⟩ := ((Nat.prime_nth_prime k).prime.dvd_finsetProd_iff _).1 h
    refine ⟨i, Finset.mem_range.1 hi, Nat.nth_injective Nat.infinite_setOfPred_prime ?_⟩
    exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_nth_prime k) (Nat.prime_nth_prime _)).1 hdvd
  · rintro ⟨i, hi, rfl⟩
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi)

/-- If the prime chosen by `T` in pair `i` divides `blockProd m U`, then `T` and `U` make the
same choice in pair `i`. -/
theorem mem_iff_of_nth_dvd {m i : ℕ} {T U : Finset ℕ}
    (h : Nat.nth Nat.Prime (2 * i + if i ∈ T then 1 else 0) ∣ blockProd m U) :
    i ∈ T ↔ i ∈ U := by
  obtain ⟨j, -, hij⟩ := nth_dvd_blockProd_iff.1 h
  obtain rfl : i = j := by split_ifs at hij <;> omega
  split_ifs at hij with h1 h2 <;> first | omega | tauto

/-- Distinct `T ⊆ {0, …, m-1}` give distinct products. -/
theorem blockProd_injOn (m : ℕ) :
    Set.InjOn (blockProd m) ((Finset.range m).powerset : Set (Finset ℕ)) := by
  intro T hT U hU hTU
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hT hU
  ext i
  by_cases him : i < m
  · have hd : Nat.nth Nat.Prime (2 * i + if i ∈ T then 1 else 0) ∣ blockProd m U := by
      rw [← hTU]
      exact nth_dvd_blockProd_iff.2 ⟨i, him, rfl⟩
    exact mem_iff_of_nth_dvd hd
  · have h1 : i ∉ T := fun h => him (Finset.mem_range.1 (hT h))
    have h2 : i ∉ U := fun h => him (Finset.mem_range.1 (hU h))
    simp [h1, h2]

/-- No three of the numbers `blockProd m T`, `T ⊆ {0, …, m-1}`, have equal pairwise gcds. -/
theorem noEqualGcd_three (m : ℕ) :
    NoEqualGcd 3 ((Finset.range m).powerset.image (blockProd m)) := by
  rintro S hS hcard ⟨d, hd⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hcard
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 (hS (by simp : x ∈ ({x, y, z} : Finset ℕ)))
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 (hS (by simp : y ∈ ({_, y, z} : Finset ℕ)))
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.1 (hS (by simp : z ∈ ({_, _, z} : Finset ℕ)))
  rw [Finset.mem_powerset] at hT hU hV
  have gxy : Nat.gcd (blockProd m T) (blockProd m U) = d := hd (by simp) (by simp) hxy
  have gxz : Nat.gcd (blockProd m T) (blockProd m V) = d := hd (by simp) (by simp) hxz
  have gyz : Nat.gcd (blockProd m U) (blockProd m V) = d := hd (by simp) (by simp) hyz
  have hTU : T ≠ U := fun h => hxy (h ▸ rfl)
  obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ T ↔ i ∈ U) := by
    by_contra h
    exact hTU (Finset.ext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have him : i < m := by
    by_cases h : i ∈ T
    · exact Finset.mem_range.1 (hT h)
    · exact Finset.mem_range.1 (hU (by tauto))
  by_cases hVT : i ∈ V ↔ i ∈ T
  · have h1 : Nat.nth Nat.Prime (2 * i + if i ∈ T then 1 else 0) ∣ blockProd m T :=
      nth_dvd_blockProd_iff.2 ⟨i, him, rfl⟩
    have h2 : Nat.nth Nat.Prime (2 * i + if i ∈ V then 1 else 0) ∣ blockProd m V :=
      nth_dvd_blockProd_iff.2 ⟨i, him, rfl⟩
    simp only [hVT] at h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [gxz, ← gxy] at h3
    exact hi (mem_iff_of_nth_dvd (h3.trans (Nat.gcd_dvd_right _ _)))
  · have hVU : i ∈ V ↔ i ∈ U := by tauto
    have h1 : Nat.nth Nat.Prime (2 * i + if i ∈ U then 1 else 0) ∣ blockProd m U :=
      nth_dvd_blockProd_iff.2 ⟨i, him, rfl⟩
    have h2 : Nat.nth Nat.Prime (2 * i + if i ∈ V then 1 else 0) ∣ blockProd m V :=
      nth_dvd_blockProd_iff.2 ⟨i, him, rfl⟩
    simp only [hVU] at h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [gyz, ← gxy] at h3
    exact hi (mem_iff_of_nth_dvd (h3.trans (Nat.gcd_dvd_left _ _))).symm

/-- If `2m ≤ π(y)`, every `blockProd m T` divides the primorial of `y`. -/
theorem blockProd_dvd_primorial {m y : ℕ} (T : Finset ℕ) (h : 2 * m ≤ Nat.primeCounting y) :
    blockProd m T ∣ primorial y := by
  set g : ℕ → ℕ := fun i => Nat.nth Nat.Prime (2 * i + if i ∈ T then 1 else 0) with hg_def
  have hg : Set.InjOn g (Finset.range m) := by
    intro i _ j _ hij
    have := Nat.nth_injective Nat.infinite_setOfPred_prime hij
    split_ifs at this <;> omega
  have e : blockProd m T = ∏ p ∈ (Finset.range m).image g, p := by
    rw [Finset.prod_image hg]
    rfl
  rw [e, primorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
  rw [Finset.mem_range] at hi
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.nth_lt_of_lt_count ?_, Nat.prime_nth_prime _⟩
  have hc : Nat.primeCounting y = Nat.count Nat.Prime (y + 1) := rfl
  split_ifs <;> omega

/-- `blockProd m T` is positive. -/
theorem blockProd_pos (m : ℕ) (T : Finset ℕ) : 0 < blockProd m T :=
  Finset.prod_pos fun _ _ => (Nat.prime_nth_prime _).pos

/-- The combinatorial core: if `4 ^ y ≤ N` then `f 3 N ≥ 2 ^ ⌊π(y)/2⌋`. -/
theorem two_pow_le_f {N y : ℕ} (hy : 4 ^ y ≤ N) : 2 ^ (Nat.primeCounting y / 2) ≤ f 3 N := by
  set m := Nat.primeCounting y / 2
  have hA : (Finset.range m).powerset.image (blockProd m) ⊆ Finset.Icc 1 N := by
    intro a ha
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 ha
    have hle : blockProd m T ≤ primorial y :=
      Nat.le_of_dvd (primorial_pos y) (blockProd_dvd_primorial T (Nat.mul_div_le _ _))
    exact Finset.mem_Icc.2 ⟨blockProd_pos m T, hle.trans ((primorial_le_four_pow y).trans hy)⟩
  have hcard := card_le_f hA (noEqualGcd_three m)
  rwa [Finset.card_image_of_injOn (blockProd_injOn m), Finset.card_powerset,
    Finset.card_range] at hcard

/-! ### Chebyshev's bound and the asymptotics -/

/-- Chebyshev's lower bound, from Mathlib: `y log 2 - log (y + 1) ≤ π(y) log y`. -/
theorem primeCounting_mul_log_ge (y : ℕ) :
    (y : ℝ) * log 2 - log ((y : ℝ) + 1) ≤ (Nat.primeCounting y : ℝ) * log y :=
  (Chebyshev.psi_ge y).trans (Chebyshev.psi_le_primeCounting_mul_log y)

/-- The quantitative bound: if `log N ≥ 512` then `N^((1/16) / log log N) < f 3 N`. -/
theorem main_bound {N : ℕ} (hN : (512 : ℝ) ≤ log N) :
    (N : ℝ) ^ ((1 / 16 : ℝ) / log (log (N : ℝ))) < (f 3 N : ℝ) := by
  set L := log (N : ℝ) with hL_def
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at hL_def
      linarith
    · exact_mod_cast h
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog4pos : 0 < log (4 : ℝ) := by rw [hlog4]; linarith
  set y := ⌊L / log 4⌋₊ with hy_def
  have hy_le : (y : ℝ) * log 4 ≤ L := by
    have := Nat.floor_le (div_nonneg (by linarith) hlog4pos.le : 0 ≤ L / log 4)
    rwa [le_div_iff₀ hlog4pos] at this
  have hy_gt : L - log 4 < (y : ℝ) * log 4 := by
    have := Nat.lt_floor_add_one (L / log 4)
    rw [div_lt_iff₀ hlog4pos] at this
    linarith
  have hy4 : 4 ^ y ≤ N := by
    have h : (4 : ℝ) ^ y ≤ N := by
      rw [← Real.log_le_log_iff (by positivity) hNpos, Real.log_pow]
      exact hy_le
    exact_mod_cast h
  set m := Nat.primeCounting y / 2 with hm_def
  have hcount : (Nat.primeCounting y : ℝ) ≤ 2 * m + 1 := by
    have : Nat.primeCounting y ≤ 2 * m + 1 := by omega
    exact_mod_cast this
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  rw [hlog4] at hy_le hy_gt
  have hy1 : (1 : ℝ) ≤ y := by nlinarith
  have hyL : (y : ℝ) + 1 ≤ L := by nlinarith
  have hLpos : 0 < L := by linarith
  have hlogL : log L ≤ L / 16 := by
    have h1 := Real.pow_div_factorial_le_exp (x := L / 16) (by positivity) 2
    have h2 : L ≤ exp (L / 16) := by
      norm_num [Nat.factorial] at h1
      nlinarith
    calc log L ≤ log (exp (L / 16)) := Real.log_le_log hLpos h2
      _ = L / 16 := Real.log_exp _
  have hlogLpos : 0 < log L := Real.log_pos (by linarith)
  have hlogy0 : 0 ≤ log (y : ℝ) := Real.log_nonneg hy1
  have hlogyL : log (y : ℝ) ≤ log L := Real.log_le_log (by linarith) (by linarith)
  have hlogy1L : log ((y : ℝ) + 1) ≤ log L := Real.log_le_log (by linarith) hyL
  have hcheb := primeCounting_mul_log_ge y
  have h1 : (Nat.primeCounting y : ℝ) * log y ≤ (2 * m + 1) * log L :=
    (mul_le_mul_of_nonneg_right hcount hlogy0).trans
      (mul_le_mul_of_nonneg_left hlogyL (by positivity))
  have hm : L / 8 < (m : ℝ) * log L := by nlinarith
  have hmpos : 0 < (m : ℝ) * log L := by linarith
  have key : L * (1 / 16 / log L) < m * log 2 := by
    rw [show L * (1 / 16 / log L) = (L / 16) / log L by ring, div_lt_iff₀ hlogLpos]
    nlinarith [mul_pos (sub_pos.2 hl2) hmpos]
  calc (N : ℝ) ^ ((1 / 16 : ℝ) / log L) = exp (L * (1 / 16 / log L)) := by
        rw [Real.rpow_def_of_pos hNpos]
    _ < exp (m * log 2) := Real.exp_lt_exp.2 key
    _ = (2 : ℝ) ^ m := by rw [Real.exp_nat_mul, Real.exp_log two_pos]
    _ ≤ f 3 N := by exact_mod_cast two_pow_le_f hy4

/-! ### Main results -/

/-- **Erdős [Er64]**, for every `r ≥ 3`: `f_r(N) > N^(c / log log N)` for all large `N`
(here with `c = 1/16` for every `r`). -/
theorem erdos_535.variants.lower_bound_of_three_le {r : ℕ} (hr : 3 ≤ r) : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) < (f r N : ℝ) := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (512 : ℝ)] with N hN
  exact (main_bound hN).trans_le (by exact_mod_cast f_mono (by norm_num) hr N)

/-- Erdős [Er64] proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$. -/
theorem erdos_535.variants.lower_bound : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) ≤ (f 3 N : ℝ) := by
  obtain ⟨c, hc, h⟩ := erdos_535.variants.lower_bound_of_three_le le_rfl
  exact ⟨c, hc, h.mono fun _ hN => hN.le⟩

end Erdos535
