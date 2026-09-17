/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-001007: the analytic input — a Chebyshev-type prime count lower bound

This file supplies the `PrimeCountInput` needed by the clustering step of the Price–GPT
counterexample (see `Jsp.Jsp001007Primes`), via the classical central-binomial-coefficient
argument:

* `4 ^ n < n * centralBinom n`                     (`Nat.four_pow_lt_mul_centralBinom`)
* primes `n < p ≤ 2n` occur in `centralBinom n` to the first power exactly,
* primes `p ≤ 2n/3` contribute at most `2n` each   (`Nat.pow_factorization_choose_le`)
* hence `4 ^ n / n < (2n) ^ (π (2n/3) + N)` where `N` is the number of primes in `(n, 2n]`.

Taking logarithms and using Mathlib's Chebyshev-type upper bound for `π`
(`Chebyshev.eventually_primeCounting_le`) gives `N ≥ c n / log n` for all large `n`.
-/

import Mathlib

open scoped BigOperators
open Filter

namespace JSP001007

/-- For a prime `p` with `n < p ≤ 2n`, the exponent of `p` in the central binomial
coefficient `centralBinom n` is exactly one. -/
theorem factorization_centralBinom_eq_one {n p : ℕ} (hp : p.Prime) (hpn : n < p)
    (hp2 : p ≤ 2 * n) : (n.centralBinom).factorization p = 1 := by
  refine le_antisymm ?_ ?_
  · -- exponent at most one: `p ^ 2 > 2 * n`
    refine Nat.factorization_choose_le_one ?_
    nlinarith [hp.two_le, hpn]
  · -- exponent at least one: `p ∣ centralBinom n`
    have hdvd : p ∣ n.centralBinom := by
      have hfact : n.centralBinom * (n.factorial * n.factorial) = (2 * n).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
        have hsub : 2 * n - n = n := by omega
        rw [hsub] at h
        rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]
        exact h
      have hp2n : p ∣ (2 * n).factorial := (Nat.Prime.dvd_factorial hp).mpr (by omega)
      rw [← hfact] at hp2n
      rcases (hp.dvd_mul).mp hp2n with h | h
      · exact h
      · exfalso
        rcases (hp.dvd_mul).mp h with h' | h' <;>
          · have := (Nat.Prime.dvd_factorial hp).mp h'
            omega
    have hpos : 0 < (n.centralBinom).factorization p := by
      rw [pos_iff_ne_zero]
      intro hzero
      rw [Nat.factorization_eq_zero_iff] at hzero
      rcases hzero with h | h | h
      · exact h hp
      · exact h hdvd
      · exact absurd h (Nat.centralBinom_ne_zero n)
    omega

/-- The central binomial coefficient splits into the contribution of the primes `≤ 2n/3`
and the contribution of the primes in `(n, 2n]` (which each occur exactly once). -/
theorem centralBinom_eq_prod {n : ℕ} (hn : 2 < n) :
    n.centralBinom =
      (∏ p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime,
          p ^ (n.centralBinom).factorization p) *
        (∏ y ∈ Finset.range n, (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y)) := by
  set f : ℕ → ℕ := fun p => p ^ (n.centralBinom).factorization p with hf
  have hsmall : ∀ p, ¬ p.Prime → f p = 1 := by
    intro p hp
    have hzero : (n.centralBinom).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_prime (n.centralBinom) hp
    simp only [hf, hzero, pow_zero]
  conv_lhs => rw [← Nat.prod_pow_factorization_centralBinom n]
  -- step 1: split `range (2n+1)` at `2n/3 + 1`
  have step1 : (∏ p ∈ Finset.range (2 * n + 1), f p) =
      (∏ p ∈ Finset.range (2 * n / 3 + 1), f p) *
        (∏ x ∈ Finset.range (2 * n + 1 - (2 * n / 3 + 1)), f (2 * n / 3 + 1 + x)) := by
    conv_lhs => rw [show 2 * n + 1 = 2 * n / 3 + 1 + (2 * n + 1 - (2 * n / 3 + 1)) by omega]
    exact Finset.prod_range_add f (2 * n / 3 + 1) (2 * n + 1 - (2 * n / 3 + 1))
  rw [step1]
  -- step 2: split the tail at `n - 2n/3`
  have step2 : (∏ x ∈ Finset.range (2 * n + 1 - (2 * n / 3 + 1)), f (2 * n / 3 + 1 + x)) =
      (∏ x ∈ Finset.range (n - 2 * n / 3), f (2 * n / 3 + 1 + x)) *
        (∏ y ∈ Finset.range n, f (2 * n / 3 + 1 + ((n - 2 * n / 3) + y))) := by
    conv_lhs => rw [show 2 * n + 1 - (2 * n / 3 + 1) = (n - 2 * n / 3) + n by omega]
    exact Finset.prod_range_add (fun x => f (2 * n / 3 + 1 + x)) (n - 2 * n / 3) n
  rw [step2]
  -- the middle factor is trivial: there `p ^ e_p = 1`
  have hmid1 : (∏ x ∈ Finset.range (n - 2 * n / 3), f (2 * n / 3 + 1 + x)) = 1 := by
    refine Finset.prod_eq_one fun x hx => ?_
    rw [Finset.mem_range] at hx
    have hpx : 2 * n / 3 + 1 + x ≤ n := by omega
    have hgt : 2 * n < 3 * (2 * n / 3 + 1 + x) := by omega
    by_cases hp : (2 * n / 3 + 1 + x).Prime
    · show (2 * n / 3 + 1 + x) ^ (n.centralBinom).factorization (2 * n / 3 + 1 + x) = 1
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpx hgt, pow_zero]
    · exact hsmall _ hp
  -- the offset identity for the large part
  have hoff : 2 * n / 3 + 1 + (n - 2 * n / 3) = n + 1 := by omega
  -- composites in the small part contribute `1`
  have hfirst : (∏ x ∈ Finset.range (2 * n / 3 + 1), f x) =
      ∏ p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime, f p := by
    refine (Finset.prod_filter_of_ne fun p _ hp => ?_).symm
    by_contra hprime
    exact hp (hsmall p hprime)
  -- rewrite the offset inside the large factor
  have hlarge : (∏ y ∈ Finset.range n, f (2 * n / 3 + 1 + ((n - 2 * n / 3) + y))) =
      ∏ y ∈ Finset.range n, f (n + 1 + y) := by
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [← add_assoc, hoff]
  rw [hfirst, hmid1, one_mul, hlarge]

/-- The number of primes in `(n, 2n]`, indexed as `n + 1 + y` for `y < n`. -/
def primeGapCount (n : ℕ) : ℕ := ((Finset.range n).filter fun y => (n + 1 + y).Prime).card

/-- The central binomial coefficient is at most `(2n)` to the power
`π (2n/3) + #{primes in (n, 2n]}`. -/
theorem centralBinom_le_pow {n : ℕ} (hn : 2 < n) :
    n.centralBinom ≤ (2 * n) ^ (Nat.primeCounting (2 * n / 3) + primeGapCount n) := by
  rw [centralBinom_eq_prod hn]
  have hA : (∏ p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime,
        p ^ (n.centralBinom).factorization p) ≤ (2 * n) ^ Nat.primeCounting (2 * n / 3) := by
    calc (∏ p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime,
            p ^ (n.centralBinom).factorization p)
        ≤ ∏ _p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime, (2 * n) := by
          refine Finset.prod_le_prod fun p _ => ?_
          exact Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) (by omega)
      _ = (2 * n) ^ Nat.primeCounting (2 * n / 3) := by
          rw [Finset.prod_const]
          congr 1
          rw [← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting]
  have hB : (∏ y ∈ Finset.range n, (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y))
      ≤ (2 * n) ^ primeGapCount n := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range n)
      (fun y => (n + 1 + y).Prime)
      (fun y => (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y))]
    have h1 : (∏ y ∈ (Finset.range n).filter (fun y => (n + 1 + y).Prime),
          (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y))
        ≤ (2 * n) ^ primeGapCount n := by
      calc (∏ y ∈ (Finset.range n).filter (fun y => (n + 1 + y).Prime),
              (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y))
          ≤ ∏ _y ∈ (Finset.range n).filter (fun y => (n + 1 + y).Prime), (2 * n) := by
            refine Finset.prod_le_prod fun y _ => ?_
            exact Nat.pow_factorization_choose_le (p := n + 1 + y) (n := 2 * n) (k := n) (by omega)
        _ = (2 * n) ^ primeGapCount n := by rw [Finset.prod_const]; rfl
    have h2 : (∏ y ∈ (Finset.range n).filter (fun y => ¬ (n + 1 + y).Prime),
          (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y)) = 1 := by
      refine Finset.prod_eq_one fun y hy => ?_
      rw [Finset.mem_filter] at hy
      rw [Nat.factorization_eq_zero_of_not_prime _ hy.2, pow_zero]
    rw [h2, mul_one]
    exact h1
  calc (∏ p ∈ (Finset.range (2 * n / 3 + 1)).filter Nat.Prime,
          p ^ (n.centralBinom).factorization p) *
        (∏ y ∈ Finset.range n, (n + 1 + y) ^ (n.centralBinom).factorization (n + 1 + y))
      ≤ (2 * n) ^ Nat.primeCounting (2 * n / 3) * (2 * n) ^ primeGapCount n :=
        Nat.mul_le_mul hA hB
    _ = (2 * n) ^ (Nat.primeCounting (2 * n / 3) + primeGapCount n) := (pow_add _ _ _).symm

/-- Chebyshev-style estimate: `4 ^ n < n * (2n) ^ (π (2n/3) + #{primes in (n, 2n]})`. -/
theorem four_pow_lt_pow {n : ℕ} (hn : 4 ≤ n) :
    4 ^ n < n * (2 * n) ^ (Nat.primeCounting (2 * n / 3) + primeGapCount n) :=
  lt_of_lt_of_le (Nat.four_pow_lt_mul_centralBinom n hn)
    (Nat.mul_le_mul_left n (centralBinom_le_pow (by omega)))

/-- **Prime count lower bound.**  Eventually, `(n, 2n]` contains at least `n / (4 log (2n))`
primes.  This is the Chebyshev-type input consumed by the clustering step. -/
theorem primeGapCount_lower :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (4 * Real.log (2 * n)) ≤ (primeGapCount n : ℝ) := by
  -- the prime counting function along `2n/3`
  have h23 : Tendsto (fun n : ℕ => 2 * n / 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (2 * b)] with n hn
    omega
  have hpi : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting (2 * n / 3) : ℝ) ≤
        (Real.log 4 + 1 / 50) * (((2 * n / 3 : ℕ)) : ℝ) /
          Real.log (((2 * n / 3 : ℕ)) : ℝ) := by
    have h := (tendsto_natCast_atTop_atTop.comp h23).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1 / 50) (by norm_num))
    filter_upwards [h] with n hn
    simpa using hn
  -- `log (2n) ≤ (9/8) log (2n/3)` eventually
  have hlogδ : ∀ᶠ n : ℕ in atTop,
      Real.log (2 * (n : ℝ)) ≤ (9 / 8) * Real.log (((2 * n / 3 : ℕ)) : ℝ) := by
    filter_upwards [eventually_ge_atTop 10000000] with n hn
    set c : ℝ := (((2 * n / 3 : ℕ)) : ℝ) with hc
    have hc1 : (1 : ℝ) ≤ c := by
      rw [hc]
      exact_mod_cast (show 1 ≤ 2 * n / 3 by omega)
    have hlogc : 8 * Real.log 6 ≤ Real.log c := by
      have h6 : (6 : ℝ) ^ 8 ≤ c := by
        rw [hc]
        exact_mod_cast (show 6 ^ 8 ≤ 2 * n / 3 by norm_num1; omega)
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (6 : ℝ) ^ 8) h6
      rwa [Real.log_pow] at h
    have h2n_le : 2 * (n : ℝ) ≤ 6 * c := by
      rw [hc]
      push_cast
      exact_mod_cast (show 2 * n ≤ 6 * (2 * n / 3) by omega)
    have hlog2n : Real.log (2 * (n : ℝ)) ≤ Real.log 6 + Real.log c := by
      calc Real.log (2 * (n : ℝ)) ≤ Real.log (6 * c) :=
            Real.log_le_log (by positivity) h2n_le
        _ = Real.log 6 + Real.log c := Real.log_mul (by norm_num) (by positivity)
    linarith
  -- `log n ≤ n/100` eventually
  have hlogε : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (1 / 100) * (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1000000] with n hn
    have h1 : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) by
      rw [Real.sqrt_eq_rpow]] at h1
    have h2 : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 200 := by
      have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
      have hnreal : (40000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 40000 ≤ n by omega)
      nlinarith [Real.sqrt_nonneg (n : ℝ), hsq, hnreal]
    linarith
  filter_upwards [hpi, hlogδ, hlogε, eventually_ge_atTop 1000000] with n hpi_n hlogδ_n hlogε_n hn
  have hn4 : 4 ≤ n := by omega
  have hn1 : (1 : ℝ) < 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hL_pos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos hn1
  -- Chebyshev's inequality, cast to `ℝ`
  have h4n : (4 : ℝ) ^ n < (n : ℝ) * (2 * (n : ℝ)) ^
      (Nat.primeCounting (2 * n / 3) + primeGapCount n) := by
    have h := four_pow_lt_pow hn4
    push_cast
    exact_mod_cast h
  have hlog4n : (n : ℝ) * Real.log 4 < Real.log (n : ℝ) +
      ((Nat.primeCounting (2 * n / 3) + primeGapCount n : ℕ) : ℝ) * Real.log (2 * (n : ℝ)) := by
    have h := Real.log_lt_log (by positivity) h4n
    rwa [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  -- numeric bounds for `log 4`
  have h4low : (1.38 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have h4high : Real.log 4 ≤ (1.39 : ℝ) := by
    have h := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  -- `π (2n/3) * log (2n)` is bounded
  have hpiL : (Nat.primeCounting (2 * n / 3) : ℝ) * Real.log (2 * (n : ℝ)) ≤
      (9 / 8) * ((Real.log 4 + 1 / 50) * (((2 * n / 3 : ℕ)) : ℝ)) := by
    have hc_pos : 0 < Real.log (((2 * n / 3 : ℕ)) : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < 2 * n / 3 by omega)
    have hpi' : (Nat.primeCounting (2 * n / 3) : ℝ) * Real.log (((2 * n / 3 : ℕ)) : ℝ) ≤
        (Real.log 4 + 1 / 50) * (((2 * n / 3 : ℕ)) : ℝ) :=
      (le_div_iff₀ hc_pos).mp hpi_n
    have hpi_nn : (0 : ℝ) ≤ (Nat.primeCounting (2 * n / 3) : ℝ) := by positivity
    calc (Nat.primeCounting (2 * n / 3) : ℝ) * Real.log (2 * (n : ℝ))
        ≤ (Nat.primeCounting (2 * n / 3) : ℝ) * ((9 / 8) * Real.log (((2 * n / 3 : ℕ)) : ℝ)) := by
          gcongr
      _ = (9 / 8) * ((Nat.primeCounting (2 * n / 3) : ℝ) *
            Real.log (((2 * n / 3 : ℕ)) : ℝ)) := by ring
      _ ≤ (9 / 8) * ((Real.log 4 + 1 / 50) * (((2 * n / 3 : ℕ)) : ℝ)) := by
          gcongr
  have hkey : (n : ℝ) * Real.log 4 - Real.log (n : ℝ) -
      (Nat.primeCounting (2 * n / 3) : ℝ) * Real.log (2 * (n : ℝ)) ≥ (n : ℝ) / 4 := by
    have hc_le : (((2 * n / 3 : ℕ)) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
      have h1 : 2 * n / 3 ≤ 2 * n / 3 := le_refl _
      have h2 : ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / 3 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
        exact_mod_cast (Nat.div_mul_le_self (2 * n) 3)
      have h3 : ((2 * n : ℕ) : ℝ) / 3 = 2 * (n : ℝ) / 3 := by push_cast; ring
      linarith
    have hb : (0 : ℝ) ≤ (((2 * n / 3 : ℕ)) : ℝ) := by positivity
    nlinarith [hpiL, hc_le, h4low, h4high, hlogε_n, hb, Nat.cast_nonneg (α := ℝ) n]
  have hNL : (primeGapCount n : ℝ) * Real.log (2 * (n : ℝ)) > (n : ℝ) / 4 := by
    have hexp : ((Nat.primeCounting (2 * n / 3) + primeGapCount n : ℕ) : ℝ) *
        Real.log (2 * (n : ℝ)) =
        (Nat.primeCounting (2 * n / 3) : ℝ) * Real.log (2 * (n : ℝ)) +
          (primeGapCount n : ℝ) * Real.log (2 * (n : ℝ)) := by
      push_cast
      ring
    nlinarith [hlog4n, hkey, hexp]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (2 * (n : ℝ)))]
  nlinarith [hNL, hL_pos]

/-- `primeGapCount n` is the number of primes in the interval `(n, 2n]`. -/
theorem primeGapCount_eq_card (n : ℕ) :
    primeGapCount n = ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  refine Finset.card_bij (fun y _ => n + 1 + y) ?_ ?_ ?_
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    have hy1' : y < n := Finset.mem_range.mp hy1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hy2⟩
  · intro y₁ _ y₂ _ h
    omega
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    have hp1' : n < p ∧ p ≤ 2 * n := Finset.mem_Ioc.mp hp1
    refine ⟨p - n - 1, ?_, by omega⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rwa [show n + 1 + (p - n - 1) = p by omega]

/-- **The Chebyshev-type prime count input** used by the clustering step, in the standard
`(n, 2n]` cardinality form. -/
theorem primeCount_lower :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (4 * Real.log (2 * n)) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [primeGapCount_lower] with n hn
  rwa [primeGapCount_eq_card] at hn

/-- `log (2n) ≤ c n` eventually, for any `c > 0`. -/
theorem eventually_log_two_mul_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (2 * (n : ℝ)) ≤ c * (n : ℝ) := by
  filter_upwards [eventually_ge_atTop ⌈8 / c ^ 2⌉₊] with n hn
  have h1 : Real.log (2 * (n : ℝ)) ≤ (2 * (n : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  rw [show (2 * (n : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt (2 * (n : ℝ)) by
    rw [Real.sqrt_eq_rpow]] at h1
  have hnbig : 8 / c ^ 2 ≤ (n : ℝ) := by
    have h3 : ((⌈8 / c ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h4 : 8 / c ^ 2 ≤ ((⌈8 / c ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have hcn : 8 ≤ c ^ 2 * (n : ℝ) := by
    have h5 := mul_le_mul_of_nonneg_right hnbig (by positivity : (0 : ℝ) ≤ c ^ 2)
    rw [div_mul_cancel₀ _ (by positivity : c ^ 2 ≠ 0), mul_comm] at h5
    exact h5
  have h2 : Real.sqrt (2 * (n : ℝ)) ≤ (c / 2) * (n : ℝ) := by
    have hy : (0 : ℝ) ≤ (c / 2) * (n : ℝ) :=
      mul_nonneg (by linarith : (0 : ℝ) ≤ c / 2) (Nat.cast_nonneg (α := ℝ) n)
    have hsq : (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith [hsq, hy, hcn, Nat.cast_nonneg (α := ℝ) n, Real.sqrt_nonneg (2 * (n : ℝ)),
      sq_nonneg ((c / 2) * (n : ℝ) - Real.sqrt (2 * (n : ℝ)))]
  linarith

/-- `log N ≤ c * N^(4/5)` eventually, for any `c > 0`. -/
theorem eventually_log_le_rpow (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ c * (N : ℝ) ^ (4 / 5 : ℝ) := by
  filter_upwards [eventually_ge_atTop ⌈(2 / c) ^ (10 / 3 : ℝ)⌉₊,
    eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h1 : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have hbig : (2 / c) ^ (10 / 3 : ℝ) ≤ (N : ℝ) := by
    have h3 : ((⌈(2 / c) ^ (10 / 3 : ℝ)⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h4 : (2 / c) ^ (10 / 3 : ℝ) ≤ ((⌈(2 / c) ^ (10 / 3 : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith
  have h2 : (2 / c) ≤ (N : ℝ) ^ (3 / 10 : ℝ) := by
    have hcpos : (0 : ℝ) < 2 / c := div_pos (by norm_num) hc
    have h5 : ((2 / c) ^ (10 / 3 : ℝ)) ^ (3 / 10 : ℝ) ≤ ((N : ℝ)) ^ (3 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbig (by norm_num)
    have h6 : ((2 / c) ^ (10 / 3 : ℝ)) ^ (3 / 10 : ℝ) = (2 / c) := by
      rw [← Real.rpow_mul hcpos.le]
      norm_num
    rwa [h6] at h5
  have h4 : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 / 10 : ℝ) = (N : ℝ) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have h5 : 2 * (N : ℝ) ^ (1 / 2 : ℝ) ≤ c * (N : ℝ) ^ (4 / 5 : ℝ) := by
    have h6 : (N : ℝ) ^ (1 / 2 : ℝ) * (2 / c) ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [h4] at h6
    have h7 : c * ((N : ℝ) ^ (1 / 2 : ℝ) * (2 / c)) = 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
      field_simp
    rw [← h7]
    exact mul_le_mul_of_nonneg_left h6 hc.le
  linarith

end JSP001007
