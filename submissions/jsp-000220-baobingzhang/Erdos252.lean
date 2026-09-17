import Mathlib

/-!
# Erdős Problem 252

Let `σ_k(n) = ∑_{d ∣ n} d ^ k`. Erdős asked whether `∑ σ_k(n) / n!` is irrational for every
`k ≥ 1`; this is open in general. We prove all the statements that formal-conjectures lists as
solved, except the unconditional cases `k = 3` (Schlage-Puchta [ScPu06]; Friedlander, Luca and
Stoiciu [FLC07]) and `k = 4` (Pratt [Pr22]), whose proofs rest on sieve methods (Chen's theorem,
Bombieri–Vinogradov) that are not available in Mathlib.

Main results:
* `summable_sigma_div_factorial`: the series converges for every `k`, so `erdos_252_sum k` is a
  genuine sum.
* `erdos_252.variants.k_eq_zero`, `erdos_252.variants.k_eq_one`, `erdos_252.variants.k_eq_two`:
  unconditional irrationality for `k = 0, 1, 2`.
* `erdos_252.variants.prime_tuples`: for `k ≥ 4`, irrationality assuming the prime `k`-tuples
  conjecture for `k` linear forms (as formalized in formal-conjectures) [FLC07, Theorem 2].
* `erdos_252.variants.schinzel`: irrationality for every `k`, assuming Schinzel's Hypothesis H (as
  formalized in formal-conjectures) [ScPu06].
* `irrational_of_good`: the arithmetic criterion behind the conditional results.

The definitions `erdos_252_sum`, `BunyakovskyCondition`, `SchinzelCondition` and the statements of
the five variants are copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/252.lean` and
`FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean`, Apache-2.0).

*References:*
 - [erdosproblems.com/252](https://www.erdosproblems.com/252)
 - [Er52] P. Erdős, Problem 4493, Amer. Math. Monthly 59 (1952); solution by J. B. Kelly (1953).
 - [ErKa54] P. Erdős, M. Kac, Problem 4518, Amer. Math. Monthly 60 (1953); solution by R. Breusch,
   Amer. Math. Monthly 61 (1954).
 - [ErSt71], [ErSt74] P. Erdős, E. G. Straus, Pacific J. Math. 36 (1971), 55 (1974).
 - [ScPu06] J.-C. Schlage-Puchta, The irrationality of a number theoretical series, Ramanujan J. 12
   (2006), 455–460.
 - [FLC07] J. B. Friedlander, F. Luca, M. Stoiciu, On the irrationality of a divisor function
   series, Integers 7 (2007), A31.
 - [Pr22] K. Pratt, The irrationality of a divisor function series of Erdős and Kac,
   arXiv:2209.11124.

## Proof for `k ≤ 2`

Write `f(n) = σ_k(n) / n!` and suppose `∑ f(n) = a / b`. Let `p = N + 1 > b` be a large
prime. Then `N! ∑ f(n)` and `N! f(n)` for `n ≤ N` are integers, hence so is
`E = σ_k(p) / p + σ_k(p + 1) / (p (p + 1)) + R`, where `R = N! ∑_{n ≥ p + 2} f(n)`.
For `k ≤ 2` we have `σ_k(n) ≤ 2 n²`, which gives `0 ≤ R ≤ 8 / p`. Now `σ_k(p) = 1 + p ^ k`, and:
* `k = 0`: `0 < E ≤ 2/p + 1/p + 8/p < 1`, using `σ_0(p + 1) ≤ p + 1`;
* `k = 1`: `1 < E ≤ 1 + 1/p + (1/2 + 1/p) + 8/p < 2`, using `2 σ_1(n) ≤ n (n + 1)`;
* `k = 2`: `p + 1 < E ≤ p + 1/p + 7/4 (1 + 1/p) + 8/p < p + 2`, using
  `n² ≤ σ_2(n) ≤ 7/4 n²` (as `∑_{d ≤ n} 1/d² ≤ 7/4`).
In each case `E` lies strictly between two consecutive integers, a contradiction.

## Conditional proof for general `k`

This follows [FLC07, Theorem 2], simplified to use one auxiliary prime. Let `k ≥ 2` and let
`p > σ_k(k)` be prime. Suppose `n` is large, `n + i = i q_i` for `1 ≤ i < k` and `n + k = k p q_k`
with large primes `q_i`, and write `a_i` for the cofactors `i` and `k p`. Let
`D_i(X) = (X + 1) ⋯ (X + i)` and divide `(X + i) ^ k = Q_i D_i + R_i` with `deg R_i < i`
(so `Q_k = 1`). Then `n! σ_k(n + i) / (n + i)! = s_i (Q_i(n) + (R_i(n) + a_i ^ k) / D_i(n))` with
`s_i = σ_k(a_i) / a_i ^ k`, and the terms with index `> n + k` contribute `O(1 / n)`. If the sum
were rational, then multiplying by `K = (k!) ^ k p ^ (k - 1)` gives `c / p + K E(n) ∈ ℤ`, where
`c = σ_k(k) (p ^ k + 1) ((k - 1)!) ^ k` is prime to `p` and `E(n) → 0`: a contradiction.

Such `n` are produced from the hypotheses via the linear forms `formA k p v * t + formB k p m v`,
whose admissibility is checked by a pigeonhole argument (`exists_forall_not_dvd`). In the
formal-conjectures statement of Hypothesis H, the variable `n` ranges over `ℤ`; we therefore use
both `A x + B` and `A x - B`, so that primes at large negative `x` are also useful.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Erdos252

open Finset ArithmeticFunction

/-- The series `∑ σ k n / n!`. -/
noncomputable def erdos_252_sum (k : ℕ) : ℝ := ∑' n, σ k n / (n ! : ℝ)

/-! ### Bounds on `σ k` -/

theorem sigma_le_pow_succ (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [sigma_apply]
  calc ∑ d ∈ n.divisors, d ^ k ≤ #n.divisors • n ^ k :=
        sum_le_card_nsmul _ _ _ fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ ≤ n * n ^ k := by
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ (k + 1) := by ring

/-- The series defining `erdos_252_sum k` converges, for every `k`. -/
theorem summable_sigma_div_factorial (k : ℕ) :
    Summable fun n => (σ k n : ℝ) / (n ! : ℝ) := by
  refine (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1))).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  gcongr
  have h1 : σ k n ≤ n ^ (k + 1) := sigma_le_pow_succ k n
  have h2 : n ^ (k + 1) ≤ (2 ^ (k + 1)) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  exact_mod_cast h1.trans h2

theorem sigma_prime (k : ℕ) {p : ℕ} (hp : p.Prime) : σ k p = 1 + p ^ k := by
  rw [sigma_apply, hp.divisors, sum_pair hp.one_lt.ne, one_pow]

theorem sum_range_inv_sq_le_aux (n : ℕ) :
    ∑ d ∈ range (n + 3), 1 / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [sum_range_succ]
  | succ n ih =>
    rw [sum_range_succ]
    have h : 1 / ((n + 3 : ℕ) : ℝ) ^ 2 ≤ 1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 1 + 2) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast at ih h ⊢
    linarith

theorem sum_range_inv_sq_le (n : ℕ) : ∑ d ∈ range n, 1 / (d : ℝ) ^ 2 ≤ 7 / 4 := by
  have h : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by positivity
  calc ∑ d ∈ range n, 1 / (d : ℝ) ^ 2 ≤ ∑ d ∈ range (n + 3), 1 / (d : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ ≤ 7 / 4 - 1 / ((n : ℝ) + 2) := sum_range_inv_sq_le_aux n
    _ ≤ 7 / 4 := by linarith

/-- For `k ≥ 2`, `σ_k(n) = ∑_{d ∣ n} (n / d)^k ≤ n^k ∑_{d ≤ n} 1 / d² ≤ 7/4 n^k`. -/
theorem sigma_le_mul_pow {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (σ k n : ℝ) ≤ 7 / 4 * (n : ℝ) ^ k := by
  rw [sigma_eq_sum_div, Nat.cast_sum]
  calc ∑ d ∈ n.divisors, (((n / d) ^ k : ℕ) : ℝ)
        = ∑ d ∈ n.divisors, (n : ℝ) ^ k * (1 / (d : ℝ) ^ k) := by
        refine sum_congr rfl fun d hd => ?_
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
        rw [Nat.cast_pow, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0, div_pow]
        field_simp
    _ ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ k * (1 / (d : ℝ) ^ 2) := by
        refine sum_le_sum fun d hd => ?_
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
        gcongr
    _ ≤ ∑ d ∈ range (n + 1), (n : ℝ) ^ k * (1 / (d : ℝ) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg
          (fun d hd => mem_range.2 (Nat.lt_succ_of_le (Nat.divisor_le hd)))
          fun _ _ _ => by positivity
    _ = (n : ℝ) ^ k * ∑ d ∈ range (n + 1), 1 / (d : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (n : ℝ) ^ k * (7 / 4) := by gcongr; exact sum_range_inv_sq_le _
    _ = 7 / 4 * (n : ℝ) ^ k := by ring

theorem sigma_two_le (n : ℕ) : (σ 2 n : ℝ) ≤ 7 / 4 * (n : ℝ) ^ 2 :=
  sigma_le_mul_pow le_rfl n

theorem two_mul_sigma_one_le (n : ℕ) : 2 * σ 1 n ≤ n * (n + 1) := by
  have h : σ 1 n ≤ ∑ i ∈ range (n + 1), i := by
    rw [sigma_one_apply]
    exact sum_le_sum_of_subset_of_nonneg
      (fun d hd => mem_range.2 (Nat.lt_succ_of_le (Nat.divisor_le hd))) fun _ _ _ => Nat.zero_le _
  have h2 := sum_range_id_mul_two (n + 1)
  rw [Nat.add_sub_cancel] at h2
  nlinarith

theorem sigma_zero_le (n : ℕ) : σ 0 n ≤ n := by
  rw [sigma_zero_apply]
  exact Nat.card_divisors_le_self n

theorem sq_le_sigma_two {n : ℕ} (hn : n ≠ 0) : n ^ 2 ≤ σ 2 n := by
  rw [sigma_apply]
  exact single_le_sum (f := fun d => d ^ 2) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn)

theorem sigma_le_two_mul_sq {k : ℕ} (hk : k ≤ 2) (n : ℕ) : (σ k n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
  interval_cases k
  · have h1 : σ 0 n ≤ n ^ 1 := sigma_le_pow_succ 0 n
    have h2 : n ^ 1 ≤ 2 * n ^ 2 := by nlinarith
    exact_mod_cast h1.trans h2
  · have h1 : σ 1 n ≤ n ^ 2 := sigma_le_pow_succ 1 n
    have h2 : n ^ 2 ≤ 2 * n ^ 2 := by omega
    exact_mod_cast h1.trans h2
  · have := sigma_two_le n
    nlinarith

/-! ### The tail estimate -/

theorem tail_aux (N j : ℕ) : (N + 3 + j) ^ 2 * N ! * (N + 1) * 2 ^ j ≤ 2 * (N + 3 + j)! := by
  induction j with
  | zero =>
    simp only [add_zero, pow_zero, mul_one]
    rw [show N + 3 = N + 2 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    calc (N + 2 + 1) ^ 2 * N ! * (N + 1) = (N + 2 + 1) * (N + 3) * ((N + 1) * N !) := by ring
      _ ≤ (N + 2 + 1) * (2 * (N + 1 + 1)) * ((N + 1) * N !) := by gcongr; omega
      _ = 2 * ((N + 2 + 1) * ((N + 1 + 1) * ((N + 1) * N !))) := by ring
  | succ j ih =>
    rw [show N + 3 + (j + 1) = N + 3 + j + 1 by ring, Nat.factorial_succ, pow_succ]
    have hm : 2 * (N + 3 + j + 1) ≤ (N + 3 + j) ^ 2 := by nlinarith
    calc (N + 3 + j + 1) ^ 2 * N ! * (N + 1) * (2 ^ j * 2)
        = (N + 3 + j + 1) * (2 * (N + 3 + j + 1)) * (N ! * (N + 1) * 2 ^ j) := by ring
      _ ≤ (N + 3 + j + 1) * (N + 3 + j) ^ 2 * (N ! * (N + 1) * 2 ^ j) := by gcongr
      _ = (N + 3 + j + 1) * ((N + 3 + j) ^ 2 * N ! * (N + 1) * 2 ^ j) := by ring
      _ ≤ (N + 3 + j + 1) * (2 * (N + 3 + j)!) := by gcongr
      _ = 2 * ((N + 3 + j + 1) * (N + 3 + j)!) := by ring

section Tail

variable {k : ℕ} (hk : ∀ n, (σ k n : ℝ) ≤ 2 * (n : ℝ) ^ 2)
include hk

theorem tail_term_le (N j : ℕ) :
    (N ! : ℝ) * ((σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ)) ≤ 8 / (N + 1) / 2 / 2 ^ j := by
  have h : (((N + 3 + j) ^ 2 * N ! * (N + 1) * 2 ^ j : ℕ) : ℝ) ≤ ((2 * (N + 3 + j)! : ℕ) : ℝ) := by
    exact_mod_cast tail_aux N j
  push_cast at h
  rw [show j + (N + 3) = N + 3 + j by ring]
  have hs := hk (N + 3 + j)
  push_cast at hs
  have hF : (0 : ℝ) < ((N + 3 + j)! : ℝ) := by positivity
  have hA : (0 : ℝ) ≤ (N ! : ℝ) * ((N : ℝ) + 1) * 2 ^ j := by positivity
  rw [show (8 : ℝ) / (N + 1) / 2 / 2 ^ j = 4 / (((N : ℝ) + 1) * 2 ^ j) by
    field_simp; ring, mul_div_assoc', div_le_div_iff₀ hF (by positivity)]
  have := mul_le_mul_of_nonneg_right hs hA
  nlinarith

theorem tail_nonneg_le (N : ℕ) :
    0 ≤ (N ! : ℝ) * ∑' j, (σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ) ∧
      (N ! : ℝ) * ∑' j, (σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ) ≤ 8 / (N + 1) := by
  rw [← tsum_mul_left]
  refine ⟨tsum_nonneg fun j => by positivity, ?_⟩
  have hs : Summable fun j => (σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ) :=
    (summable_nat_add_iff (f := fun n => (σ k n : ℝ) / (n ! : ℝ)) (N + 3)).2
      (summable_sigma_div_factorial k)
  calc ∑' j, (N ! : ℝ) * ((σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ))
      ≤ ∑' j : ℕ, 8 / ((N : ℝ) + 1) / 2 / 2 ^ j :=
        (hs.mul_left _).tsum_le_tsum (tail_term_le hk N) (summable_geometric_two' _)
    _ = 8 / (N + 1) := tsum_geometric_two' _

/-- If `erdos_252_sum k` is rational then, for arbitrarily large primes `p`,
`σ_k(p) / p + σ_k(p + 1) / (p (p + 1)) + R` is an integer for some `0 ≤ R ≤ 8 / p`. -/
theorem exists_int_of_not_irrational (h : ¬ Irrational (erdos_252_sum k)) (M : ℕ) :
    ∃ p : ℕ, M ≤ p ∧ p.Prime ∧ ∃ R : ℝ, 0 ≤ R ∧ R ≤ 8 / p ∧ ∃ z : ℤ,
      (σ k p : ℝ) / p + (σ k (p + 1) : ℝ) / (p * (p + 1)) + R = z := by
  obtain ⟨q, hq⟩ : erdos_252_sum k ∈ Set.range ((↑) : ℚ → ℝ) := not_not.1 h
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (M + q.den + 1)
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := ⟨p - 1, by omega⟩
  refine ⟨N + 1, by omega, hpp, _, (tail_nonneg_le hk N).1, by
    push_cast; exact (tail_nonneg_le hk N).2, ?_⟩
  have hden : q.den ∣ N ! := Nat.dvd_factorial q.den_pos (by omega)
  refine ⟨q.num * ((N ! / q.den : ℕ) : ℤ) -
    ∑ n ∈ range (N + 1), ((σ k n * (N ! / n !) : ℕ) : ℤ), ?_⟩
  set f : ℕ → ℝ := fun n => (σ k n : ℝ) / (n ! : ℝ) with hf
  have hsplit := (summable_sigma_div_factorial k).sum_add_tsum_nat_add (N + 3)
  have hq' : (q : ℝ) = ∑ n ∈ range (N + 3), f n +
      ∑' j, (σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ) := by
    rw [hq]
    exact hsplit.symm
  have hfac0 : (N ! : ℝ) ≠ 0 := by positivity
  have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have e1 : ((q.num * ((N ! / q.den : ℕ) : ℤ) : ℤ) : ℝ) = (N ! : ℝ) * q := by
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hden hden0, Rat.cast_def]
    field_simp
  have e2 : (((∑ n ∈ range (N + 1), ((σ k n * (N ! / n !) : ℕ) : ℤ)) : ℤ) : ℝ) =
      ∑ n ∈ range (N + 1), (N ! : ℝ) * f n := by
    rw [Int.cast_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hn)
    rw [Int.cast_natCast, Nat.cast_mul,
      Nat.cast_div (Nat.factorial_dvd_factorial hn') (by positivity)]
    simp only [hf]
    ring
  have e3 : (N ! : ℝ) * f (N + 1) = (σ k (N + 1) : ℝ) / ((N : ℝ) + 1) := by
    simp only [hf, Nat.factorial_succ]
    push_cast
    field_simp
  have e4 : (N ! : ℝ) * f (N + 2) =
      (σ k (N + 1 + 1) : ℝ) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) := by
    simp only [hf, show N + 2 = N + 1 + 1 from rfl, Nat.factorial_succ]
    push_cast
    field_simp
  have e5 : (N ! : ℝ) * q = ∑ n ∈ range (N + 1), (N ! : ℝ) * f n + (N ! : ℝ) * f (N + 1) +
      (N ! : ℝ) * f (N + 2) +
      (N ! : ℝ) * ∑' j, (σ k (j + (N + 3)) : ℝ) / ((j + (N + 3))! : ℝ) := by
    rw [hq', sum_range_succ, sum_range_succ, mul_add, mul_add, mul_add, mul_sum]
  rw [Int.cast_sub, e1, e2, e5, e3, e4]
  push_cast
  ring

end Tail

/-! ### The three cases -/

/-- `∑ σ 0 n / n!` is irrational. This is proved in [ErSt71]. -/
theorem erdos_252.variants.k_eq_zero : Irrational (erdos_252_sum 0) := by
  intro h
  obtain ⟨p, hp, hpp, R, hR0, hR, z, hz⟩ :=
    exists_int_of_not_irrational (sigma_le_two_mul_sq (k := 0) (by norm_num))
      (fun h' => h' h) 200
  have hp' : (200 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (σ 0 p : ℝ) / p = 2 * (1 / p) := by
    rw [sigma_prime 0 hpp]
    push_cast
    ring
  have h2 : (σ 0 (p + 1) : ℝ) / (p * (p + 1)) ≤ 1 / p := by
    have : (σ 0 (p + 1) : ℝ) ≤ p + 1 := by exact_mod_cast sigma_zero_le (p + 1)
    rw [div_le_div_iff₀ (by positivity) hp0]
    nlinarith
  have h3 : (0 : ℝ) ≤ (σ 0 (p + 1) : ℝ) / (p * (p + 1)) := by positivity
  have h4 : 1 / (p : ℝ) ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) hp'
  have h5 : (0 : ℝ) < 1 / p := by positivity
  rw [h1] at hz
  have hR' : R ≤ 8 * (1 / p) := by rw [mul_one_div]; exact hR
  have hlo : (0 : ℝ) < z := by linarith
  have hhi : (z : ℝ) < 1 := by linarith
  have hlo' : (0 : ℤ) < z := by exact_mod_cast hlo
  have hhi' : z < 1 := by exact_mod_cast hhi
  omega

/-- `∑ σ 1 n / n!` is irrational. This is proved in [ErSt74]. -/
theorem erdos_252.variants.k_eq_one : Irrational (erdos_252_sum 1) := by
  intro h
  obtain ⟨p, hp, hpp, R, hR0, hR, z, hz⟩ :=
    exists_int_of_not_irrational (sigma_le_two_mul_sq (k := 1) (by norm_num))
      (fun h' => h' h) 200
  have hp' : (200 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (σ 1 p : ℝ) / p = 1 + 1 / p := by
    rw [sigma_prime 1 hpp]
    push_cast
    field_simp
    ring
  have h2 : (σ 1 (p + 1) : ℝ) / (p * (p + 1)) ≤ 1 / 2 + 1 / p := by
    have : ((2 * σ 1 (p + 1) : ℕ) : ℝ) ≤ ((p + 1) * (p + 1 + 1) : ℕ) := by
      exact_mod_cast two_mul_sigma_one_le (p + 1)
    push_cast at this
    rw [div_le_iff₀ (by positivity),
      show (1 / 2 + 1 / (p : ℝ)) * (p * (p + 1)) = ((p : ℝ) + 1) * (p + 1 + 1) / 2 by
        field_simp; ring]
    linarith
  have h3 : (0 : ℝ) ≤ (σ 1 (p + 1) : ℝ) / (p * (p + 1)) := by positivity
  have h4 : 1 / (p : ℝ) ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) hp'
  have h5 : (0 : ℝ) < 1 / p := by positivity
  rw [h1] at hz
  have hR' : R ≤ 8 * (1 / p) := by rw [mul_one_div]; exact hR
  have hlo : (1 : ℝ) < z := by linarith
  have hhi : (z : ℝ) < 2 := by linarith
  have hlo' : (1 : ℤ) < z := by exact_mod_cast hlo
  have hhi' : z < 2 := by exact_mod_cast hhi
  omega

/-- `∑ σ 2 n / n!` is irrational. This is proved in [ErKa54]. -/
theorem erdos_252.variants.k_eq_two : Irrational (erdos_252_sum 2) := by
  intro h
  obtain ⟨p, hp, hpp, R, hR0, hR, z, hz⟩ :=
    exists_int_of_not_irrational (sigma_le_two_mul_sq le_rfl) (fun h' => h' h) 200
  have hp' : (200 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (σ 2 p : ℝ) / p = p + 1 / p := by
    rw [sigma_prime 2 hpp]
    push_cast
    field_simp
    ring
  have h2 : (σ 2 (p + 1) : ℝ) / (p * (p + 1)) ≤ 7 / 4 + 7 / 4 * (1 / p) := by
    have := sigma_two_le (p + 1)
    push_cast at this
    rw [div_le_iff₀ (by positivity),
      show (7 / 4 + 7 / 4 * (1 / (p : ℝ))) * (p * (p + 1)) = 7 / 4 * ((p : ℝ) + 1) ^ 2 by
        field_simp]
    exact this
  have h3 : 1 + 1 / (p : ℝ) ≤ (σ 2 (p + 1) : ℝ) / (p * (p + 1)) := by
    have : (((p + 1) ^ 2 : ℕ) : ℝ) ≤ (σ 2 (p + 1) : ℝ) := by
      exact_mod_cast sq_le_sigma_two (Nat.succ_ne_zero p)
    push_cast at this
    rw [le_div_iff₀ (by positivity),
      show (1 + 1 / (p : ℝ)) * (p * (p + 1)) = ((p : ℝ) + 1) ^ 2 by field_simp]
    exact this
  have h4 : 1 / (p : ℝ) ≤ 1 / 200 := one_div_le_one_div_of_le (by norm_num) hp'
  have h5 : (0 : ℝ) < 1 / p := by positivity
  rw [h1] at hz
  have hR' : R ≤ 8 * (1 / p) := by rw [mul_one_div]; exact hR
  have hlo : (p : ℝ) + 1 < z := by linarith
  have hhi : (z : ℝ) < p + 2 := by linarith
  have hlo' : (p : ℤ) + 1 < z := by exact_mod_cast hlo
  have hhi' : z < (p : ℤ) + 2 := by exact_mod_cast hhi
  omega

/-! ## General `k`: the conditional results

The remaining results follow Friedlander, Luca and Stoiciu [FLC07, Theorem 2] (see also
Schlage-Puchta [ScPu06]), in a slightly simplified form that uses a single auxiliary prime `p`.
-/

open Polynomial Filter Topology

/-! ### Tail estimate for `k ≥ 2` -/

theorem pow_le_mul_descFactorial {m k : ℕ} (hkm : k ≤ m) :
    m ^ k ≤ (k + 1) ^ k * m.descFactorial k := by
  have h1 := Nat.pow_sub_le_descFactorial m k
  have h2 : m ≤ (k + 1) * (m + 1 - k) := by
    obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
    rw [show k + d + 1 - k = d + 1 by omega]
    nlinarith
  calc m ^ k ≤ ((k + 1) * (m + 1 - k)) ^ k := Nat.pow_le_pow_left h2 k
    _ = (k + 1) ^ k * (m + 1 - k) ^ k := mul_pow _ _ _
    _ ≤ (k + 1) ^ k * m.descFactorial k := Nat.mul_le_mul_left _ h1

theorem factorial_mul_two_pow_le (n j : ℕ) : n ! * (n + 1) * 2 ^ j ≤ (n + 1 + j)! := by
  induction j with
  | zero => simp [Nat.factorial_succ, mul_comm]
  | succ j ih =>
    rw [show n + 1 + (j + 1) = n + 1 + j + 1 by ring, Nat.factorial_succ, pow_succ]
    calc n ! * (n + 1) * (2 ^ j * 2) = 2 * (n ! * (n + 1) * 2 ^ j) := by ring
      _ ≤ (n + 1 + j + 1) * (n + 1 + j)! := by gcongr; omega

section GeneralTail

variable {k : ℕ} (hk : 2 ≤ k)
include hk

theorem tail_term_le_general (n j : ℕ) :
    (n ! : ℝ) * ((σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ)) ≤
      4 * (k + 1) ^ k / (n + 1) / 2 / 2 ^ j := by
  set m := j + (n + 1 + k) with hm
  have hkm : k ≤ m := by omega
  have hfac : ((m - k)! : ℝ) * (m.descFactorial k : ℝ) = (m ! : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hkm
  have hmk : m - k = n + 1 + j := by omega
  rw [hmk] at hfac
  have h1 := sigma_le_mul_pow hk m
  have h2 : ((m ^ k : ℕ) : ℝ) ≤ (((k + 1) ^ k * m.descFactorial k : ℕ) : ℝ) := by
    exact_mod_cast pow_le_mul_descFactorial hkm
  have h3 : ((n ! * (n + 1) * 2 ^ j : ℕ) : ℝ) ≤ ((n + 1 + j)! : ℝ) := by
    exact_mod_cast factorial_mul_two_pow_le n j
  push_cast at h2 h3
  have hD : (0 : ℝ) < (m.descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hkm
  have hF : (0 : ℝ) < ((n + 1 + j)! : ℝ) := by positivity
  rw [← hfac, show (4 : ℝ) * (k + 1) ^ k / (n + 1) / 2 / 2 ^ j =
    2 * (k + 1) ^ k / (((n : ℝ) + 1) * 2 ^ j) by field_simp; ring, mul_div_assoc',
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hσ : (σ k m : ℝ) ≤ 2 * ((k : ℝ) + 1) ^ k * (m.descFactorial k : ℝ) := by nlinarith
  have hn0 : (0 : ℝ) ≤ (n ! : ℝ) := by positivity
  calc (n ! : ℝ) * (σ k m : ℝ) * (((n : ℝ) + 1) * 2 ^ j)
      ≤ (n ! : ℝ) * (2 * ((k : ℝ) + 1) ^ k * (m.descFactorial k : ℝ)) *
          (((n : ℝ) + 1) * 2 ^ j) := by
        gcongr
    _ = 2 * ((k : ℝ) + 1) ^ k * (m.descFactorial k : ℝ) * ((n ! : ℝ) * ((n : ℝ) + 1) * 2 ^ j) := by
        ring
    _ ≤ 2 * ((k : ℝ) + 1) ^ k * (m.descFactorial k : ℝ) * ((n + 1 + j)! : ℝ) := by gcongr
    _ = 2 * ((k : ℝ) + 1) ^ k * (((n + 1 + j)! : ℝ) * (m.descFactorial k : ℝ)) := by ring

theorem tail_nonneg_le_general (n : ℕ) :
    0 ≤ (n ! : ℝ) * ∑' j, (σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ) ∧
      (n ! : ℝ) * ∑' j, (σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ) ≤
        4 * (k + 1) ^ k / (n + 1) := by
  rw [← tsum_mul_left]
  refine ⟨tsum_nonneg fun j => by positivity, ?_⟩
  have hs : Summable fun j => (σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ) :=
    (summable_nat_add_iff (f := fun n => (σ k n : ℝ) / (n ! : ℝ)) (n + 1 + k)).2
      (summable_sigma_div_factorial k)
  calc ∑' j, (n ! : ℝ) * ((σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ))
      ≤ ∑' j : ℕ, 4 * ((k : ℝ) + 1) ^ k / ((n : ℝ) + 1) / 2 / 2 ^ j :=
        (hs.mul_left _).tsum_le_tsum (tail_term_le_general hk n) (summable_geometric_two' _)
    _ = 4 * (k + 1) ^ k / (n + 1) := tsum_geometric_two' _

end GeneralTail

/-! ### Polynomial division by `(X + 1) ⋯ (X + i)` -/

/-- `D i = (X + 1) (X + 2) ⋯ (X + i)`. -/
noncomputable def D (i : ℕ) : ℤ[X] := ∏ j ∈ range i, (X + C ((j : ℤ) + 1))

theorem D_monic (i : ℕ) : (D i).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem D_natDegree (i : ℕ) : (D i).natDegree = i := by
  rw [D, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

theorem D_degree (i : ℕ) : (D i).degree = i := by
  rw [degree_eq_natDegree (D_monic i).ne_zero, D_natDegree]

theorem factorial_mul_eval_D (n i : ℕ) :
    (n ! : ℤ) * (D i).eval (n : ℤ) = ((n + i)! : ℤ) := by
  induction i with
  | zero => simp [D]
  | succ i ih =>
    rw [D, prod_range_succ, eval_mul, ← D, ← mul_assoc, ih,
      show n + (i + 1) = n + i + 1 by ring, Nat.factorial_succ]
    simp only [eval_add, eval_X, eval_C]
    push_cast
    ring

theorem eval_D_pos (n i : ℕ) : 0 < (D i).eval (n : ℤ) := by
  have h := factorial_mul_eval_D n i
  have h1 : (0 : ℤ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have h2 : (0 : ℤ) < (n + i)! := by exact_mod_cast Nat.factorial_pos _
  by_contra h3
  push Not at h3
  nlinarith

/-- `(X + i) ^ k`. -/
noncomputable def F (k i : ℕ) : ℤ[X] := (X + C (i : ℤ)) ^ k

theorem eval_F_decomp (k i : ℕ) (x : ℤ) :
    (x + i) ^ k = (F k i %ₘ D i).eval x + (D i).eval x * (F k i /ₘ D i).eval x := by
  have h := congrArg (eval x) (modByMonic_add_div (F k i) (D i))
  simp only [F, eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
  simp only [F]
  exact h.symm

theorem F_divByMonic_D_self (k : ℕ) : F k k /ₘ D k = 1 := by
  have hF : (F k k).degree = k := by
    rw [F, degree_pow, degree_X_add_C, nsmul_one]
  have hFm : (F k k).Monic := (monic_X_add_C _).pow k
  refine (div_modByMonic_unique 1 (F k k - D k) (D_monic k) ⟨by ring, ?_⟩).1
  rw [D_degree]
  calc (F k k - D k).degree < (F k k).degree :=
        degree_sub_lt_left (by rw [hF, D_degree]) hFm.ne_zero
          (by rw [hFm.leadingCoeff, (D_monic k).leadingCoeff])
    _ = k := hF

theorem tendsto_modByMonic_D (k i : ℕ) (hi : 1 ≤ i) (e : ℤ) :
    Tendsto (fun n : ℕ => (((F k i %ₘ D i).eval (n : ℤ) + e : ℤ) : ℝ) /
      (((D i).eval (n : ℤ) : ℤ) : ℝ)) atTop (𝓝 0) := by
  set P : ℝ[X] := (F k i %ₘ D i + C e).map (Int.castRingHom ℝ)
  set Q : ℝ[X] := (D i).map (Int.castRingHom ℝ)
  have hdeg : P.degree < Q.degree := by
    rw [degree_map_eq_of_injective Int.cast_injective,
      degree_map_eq_of_injective Int.cast_injective]
    calc (F k i %ₘ D i + C e).degree ≤ max (F k i %ₘ D i).degree (C e).degree :=
          degree_add_le _ _
      _ < (D i).degree := by
          refine max_lt (degree_modByMonic_lt _ (D_monic i)) ?_
          rw [D_degree]
          exact degree_C_le.trans_lt (by exact_mod_cast hi)
  refine ((div_tendsto_atTop_zero_of_degree_lt P Q hdeg).comp
    tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [P, Q, Function.comp_apply, eval_natCast_map, eq_intCast, eval_add, eval_intCast]
  push_cast
  rfl

/-! ### The core of the conditional argument -/

/-- The cofactors `a_i`: `i` for `i < k`, and `k p` for `i = k`. -/
def cof (k p i : ℕ) : ℕ := if i < k then i else k * p

theorem exists_int_of_rat {k : ℕ} {r : ℚ} (hr : (r : ℝ) = erdos_252_sum k) {n : ℕ}
    (hn : r.den ≤ n) (L : ℕ) :
    ∃ z : ℤ, ∑ v ∈ range L, (n ! : ℝ) * ((σ k (n + 1 + v) : ℝ) / ((n + 1 + v)! : ℝ)) +
      (n ! : ℝ) * ∑' j, (σ k (j + (n + 1 + L)) : ℝ) / ((j + (n + 1 + L))! : ℝ) = z := by
  have hden : r.den ∣ n ! := Nat.dvd_factorial r.den_pos hn
  refine ⟨r.num * ((n ! / r.den : ℕ) : ℤ) -
    ∑ m ∈ range (n + 1), ((σ k m * (n ! / m !) : ℕ) : ℤ), ?_⟩
  have hsplit := (summable_sigma_div_factorial k).sum_add_tsum_nat_add (n + 1 + L)
  rw [sum_range_add] at hsplit
  have hden0 : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have e1 : ((r.num * ((n ! / r.den : ℕ) : ℤ) : ℤ) : ℝ) = (n ! : ℝ) * r := by
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hden hden0, Rat.cast_def]
    field_simp
  have e2 : (((∑ m ∈ range (n + 1), ((σ k m * (n ! / m !) : ℕ) : ℤ)) : ℤ) : ℝ) =
      (n ! : ℝ) * ∑ m ∈ range (n + 1), (σ k m : ℝ) / (m ! : ℝ) := by
    rw [Int.cast_sum, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm' : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
    rw [Int.cast_natCast, Nat.cast_mul,
      Nat.cast_div (Nat.factorial_dvd_factorial hm') (by positivity)]
    ring
  rw [Int.cast_sub, e1, e2, hr, erdos_252_sum, ← hsplit, ← mul_sum]
  ring

theorem term_eq {k n i a q : ℕ} (ha : 0 < a) (hq : q.Prime) (haq : a < q) (hn : n + i = a * q) :
    (n ! : ℝ) * ((σ k (n + i) : ℝ) / ((n + i)! : ℝ)) =
      (σ k a : ℝ) / (a : ℝ) ^ k * (((F k i /ₘ D i).eval (n : ℤ) : ℤ) : ℝ) +
      (σ k a : ℝ) / (a : ℝ) ^ k * ((((F k i %ₘ D i).eval (n : ℤ) + (a : ℤ) ^ k : ℤ) : ℝ) /
        (((D i).eval (n : ℤ) : ℤ) : ℝ)) := by
  have hcop : Nat.Coprime a q :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      fun h => absurd (Nat.le_of_dvd ha h) (by omega))
  have hσ : σ k (n + i) = σ k a * (1 + q ^ k) := by
    rw [hn, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime k hq]
  have hfac : ((n + i)! : ℝ) = (n ! : ℝ) * (((D i).eval (n : ℤ) : ℤ) : ℝ) := by
    have := factorial_mul_eval_D n i
    exact_mod_cast this.symm
  have hdec := eval_F_decomp k i (n : ℤ)
  have h2 : ((n : ℤ) + i) = (a : ℤ) * q := by exact_mod_cast hn
  rw [h2] at hdec
  have hdec' : ((a : ℝ) * q) ^ k = (((F k i %ₘ D i).eval (n : ℤ) : ℤ) : ℝ) +
      (((D i).eval (n : ℤ) : ℤ) : ℝ) * (((F k i /ₘ D i).eval (n : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hdec
  have hD : (0 : ℝ) < (((D i).eval (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast eval_D_pos n i
  have hfpos : (0 : ℝ) < n ! := by positivity
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [hfac, hσ]
  push_cast
  field_simp
  rw [mul_pow] at hdec'
  linear_combination hdec'

theorem tendsto_error {k : ℕ} (hk : 2 ≤ k) (s : ℕ → ℝ) (e : ℕ → ℤ) :
    Tendsto (fun n : ℕ => ∑ v ∈ range k, s v *
      ((((F k (v + 1) %ₘ D (v + 1)).eval (n : ℤ) + e v : ℤ) : ℝ) /
        (((D (v + 1)).eval (n : ℤ) : ℤ) : ℝ)) +
      (n ! : ℝ) * ∑' j, (σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ))
      atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ v ∈ range k, s v * 0 + 0 by simp]
  refine Tendsto.add (tendsto_finsetSum _ fun v _ =>
    (tendsto_modByMonic_D k (v + 1) (by omega) (e v)).const_mul (s v)) ?_
  have hup : Tendsto (fun n : ℕ => 4 * ((k : ℝ) + 1) ^ k * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * ((k : ℝ) + 1) ^ k)
  refine squeeze_zero (fun n => (tail_nonneg_le_general hk n).1) (fun n => ?_) hup
  rw [mul_one_div]
  exact (tail_nonneg_le_general hk n).2

theorem one_div_le_abs_sub {p c : ℕ} (hp : 0 < p) (hpc : ¬ p ∣ c) (w : ℤ) :
    1 / (p : ℝ) ≤ |(w : ℝ) - c / p| := by
  have hne : w * p - c ≠ 0 := by
    intro h
    apply hpc
    have h' : (c : ℤ) = w * p := by linarith
    exact Int.natCast_dvd_natCast.1 ⟨w, by rw [h']; ring⟩
  have h1 : (1 : ℝ) ≤ |((w * p - c : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [show (w : ℝ) - c / p = ((w * p - c : ℤ) : ℝ) / p by push_cast; field_simp, abs_div,
    abs_of_pos hp']
  exact div_le_div_of_nonneg_right h1 hp'.le

theorem self_le_sigma_self (k : ℕ) (hk : 1 ≤ k) : k ≤ σ k k := by
  have h1 : k ^ k ≤ σ k k := by
    rw [sigma_apply]
    exact single_le_sum (f := fun d => d ^ k) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self k (by omega))
  exact (Nat.le_self_pow (by omega) k).trans h1

/-- **Core of the conditional argument** (Friedlander–Luca–Stoiciu, Schlage-Puchta). Let
`k ≥ 2` and let `p > σ_k(k)` be prime. If there are arbitrarily large `n` such that `n + i = i q_i`
for `1 ≤ i < k` and `n + k = k p q_k`, with primes `q_i` larger than the cofactors, then
`∑ σ_k(n) / n!` is irrational. -/
theorem irrational_of_good {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hpk : σ k k < p)
    (hgood : ∀ M, ∃ n, M ≤ n ∧ ∀ i, 1 ≤ i → i ≤ k →
      ∃ q, q.Prime ∧ cof k p i < q ∧ n + i = cof k p i * q) :
    Irrational (erdos_252_sum k) := by
  rintro ⟨r, hr⟩
  set s : ℕ → ℝ := fun v => (σ k (cof k p (v + 1)) : ℝ) / (cof k p (v + 1) : ℝ) ^ k with hs
  set Q : ℕ → ℕ → ℝ := fun v n => (((F k (v + 1) /ₘ D (v + 1)).eval (n : ℤ) : ℤ) : ℝ) with hQ
  set E : ℕ → ℝ := fun n => ∑ v ∈ range k, s v *
      ((((F k (v + 1) %ₘ D (v + 1)).eval (n : ℤ) + (cof k p (v + 1) : ℤ) ^ k : ℤ) : ℝ) /
        (((D (v + 1)).eval (n : ℤ) : ℤ) : ℝ)) +
      (n ! : ℝ) * ∑' j, (σ k (j + (n + 1 + k)) : ℝ) / ((j + (n + 1 + k))! : ℝ) with hE
  have hEt : Tendsto E atTop (𝓝 0) := tendsto_error hk s _
  set K : ℕ := (k !) ^ k * p ^ (k - 1) with hK
  set c : ℕ := σ k k * (1 + p ^ k) * ((k - 1)!) ^ k with hc
  have hkp : k < p := lt_of_le_of_lt (self_le_sigma_self k (by omega)) hpk
  have hpc : ¬ p ∣ c := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := Nat.le_of_dvd (ArithmeticFunction.sigma_pos k k (by omega)) h
        omega
      · have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
        have := (Nat.dvd_add_left h1).1 h
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    · have := (Nat.Prime.dvd_factorial hp).1 (hp.dvd_of_dvd_pow h)
      omega
  have hKE : ∀ᶠ n in atTop, |(K : ℝ) * E n| < 1 / p := by
    have h := (hEt.const_mul (K : ℝ)).abs
    rw [mul_zero, abs_zero] at h
    have hp0 : (0 : ℝ) < 1 / p := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    exact h.eventually (gt_mem_nhds hp0)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hKE
  obtain ⟨n, hn, hgn⟩ := hgood (max M r.den)
  obtain ⟨z, hz⟩ := exists_int_of_rat hr (le_of_max_le_right hn) k
  have hterm : ∀ v ∈ range k, (n ! : ℝ) * ((σ k (n + 1 + v) : ℝ) / ((n + 1 + v)! : ℝ)) =
      s v * Q v n + s v *
      ((((F k (v + 1) %ₘ D (v + 1)).eval (n : ℤ) + (cof k p (v + 1) : ℤ) ^ k : ℤ) : ℝ) /
        (((D (v + 1)).eval (n : ℤ) : ℤ) : ℝ)) := by
    intro v hv
    have hv' := mem_range.1 hv
    obtain ⟨q, hq, hlt, heq⟩ := hgn (v + 1) (by omega) (by omega)
    have ha : 0 < cof k p (v + 1) := by
      unfold cof
      split_ifs
      · omega
      · exact Nat.mul_pos (by omega) hp.pos
    rw [show n + 1 + v = n + (v + 1) by ring]
    exact term_eq ha hq hlt heq
  rw [sum_congr rfl hterm, sum_add_distrib, add_assoc] at hz
  have hsplit := sum_range_succ (fun v => s v * Q v n) (k - 1)
  rw [show k - 1 + 1 = k by omega] at hsplit
  rw [hsplit] at hz
  have hlast : (K : ℝ) * (s (k - 1) * Q (k - 1) n) = c / p := by
    have hcof : cof k p (k - 1 + 1) = k * p := by
      simp only [cof, show ¬ (k - 1 + 1 < k) by omega, ↓reduceIte]
    have hcop : Nat.Coprime k p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
        fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))
    have hQ1 : Q (k - 1) n = 1 := by
      simp only [hQ, show k - 1 + 1 = k by omega, F_divByMonic_D_self, eval_one, Int.cast_one]
    have hσ : σ k (k * p) = σ k k * (1 + p ^ k) := by
      rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime k hp]
    have hfac : ((k ! : ℕ) : ℝ) = (k : ℝ) * ((k - 1)! : ℕ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : k ≠ 0)).symm
    have hpk1 : (p : ℝ) ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ', show k - 1 + 1 = k by omega]
    simp only [hs, hQ1, hcof, hσ, hK, hc]
    push_cast
    rw [hfac, hpk1]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    field_simp
    rw [mul_pow (k : ℝ) (p : ℝ), hpk1]
    ring
  have hint : ∃ Z : ℤ, (K : ℝ) * ∑ v ∈ range (k - 1), s v * Q v n = Z := by
    refine ⟨∑ v ∈ range (k - 1), ((σ k (v + 1) * (k ! / (v + 1)) ^ k * p ^ (k - 1) : ℕ) : ℤ) *
      (F k (v + 1) /ₘ D (v + 1)).eval (n : ℤ), ?_⟩
    rw [mul_sum, Int.cast_sum]
    refine sum_congr rfl fun v hv => ?_
    have hv' := mem_range.1 hv
    have hcof : cof k p (v + 1) = v + 1 := by
      simp only [cof, show v + 1 < k by omega, ↓reduceIte]
    have hdvd : v + 1 ∣ k ! := Nat.dvd_factorial (by omega) (by omega)
    simp only [hs, hQ, hcof, hK, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_mul,
      Nat.cast_pow]
    rw [Nat.cast_div hdvd (by positivity : ((v + 1 : ℕ) : ℝ) ≠ 0)]
    push_cast
    have hv0 : (0 : ℝ) < (v : ℝ) + 1 := by positivity
    rw [div_pow]
    field_simp
  obtain ⟨Z, hZ⟩ := hint
  have key : (K : ℝ) * E n = ((K * z - Z : ℤ) : ℝ) - c / p := by
    push_cast
    rw [← hz, ← hZ, ← hlast]
    simp only [hE]
    ring
  have h1 := one_div_le_abs_sub hp.pos hpc (K * z - Z)
  have h2 := hM n (le_of_max_le_left hn)
  rw [key] at h2
  linarith

/-! ### Construction of the linear forms -/

/-- Pigeonhole: if every form `A_j t + B_j` vanishes modulo `ℓ` for at most one residue `t`
(and for none if `ℓ ∣ A_j`), then some `t ≤ #S` makes all of them nonzero modulo `ℓ`. -/
theorem exists_forall_not_dvd {ι : Type*} (S : Finset ι) (A B : ι → ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ∀ j ∈ S, ((ℓ : ℤ) ∣ A j → ¬ (ℓ : ℤ) ∣ B j) ∧ (¬ (ℓ : ℤ) ∣ A j → #S < ℓ)) :
    ∃ t : ℕ, ∀ j ∈ S, ¬ (ℓ : ℤ) ∣ A j * t + B j := by
  classical
  set bad : ι → Finset ℕ := fun j => (range (#S + 1)).filter fun t => (ℓ : ℤ) ∣ A j * t + B j
  have hbad : ∀ j ∈ S, #(bad j) ≤ 1 := by
    intro j hj
    refine card_le_one.2 fun t ht t' ht' => ?_
    simp only [bad, mem_filter, mem_range] at ht ht'
    have hsub : (ℓ : ℤ) ∣ A j * ((t : ℤ) - t') := by
      have := dvd_sub ht.2 ht'.2
      rw [show A j * (t : ℤ) + B j - (A j * t' + B j) = A j * ((t : ℤ) - t') by ring] at this
      exact this
    by_cases hA : (ℓ : ℤ) ∣ A j
    · exact absurd ((dvd_add_right (dvd_mul_of_dvd_left hA _)).1 ht.2) ((h j hj).1 hA)
    · have hlt := (h j hj).2 hA
      have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
      rcases hℓ'.dvd_or_dvd hsub with h1 | h1
      · exact absurd h1 hA
      · have habs : |(t : ℤ) - t'| < ℓ := by
          rw [abs_lt]
          constructor <;> omega
        have := Int.eq_zero_of_abs_lt_dvd h1 habs
        omega
  have hcard : #(S.biUnion bad) < #(range (#S + 1)) := by
    rw [card_range]
    calc #(S.biUnion bad) ≤ ∑ j ∈ S, #(bad j) := card_biUnion_le
      _ ≤ ∑ _j ∈ S, 1 := sum_le_sum hbad
      _ = #S := by simp
      _ < #S + 1 := Nat.lt_succ_self _
  obtain ⟨t, ht, hnot⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨t, fun j hj hdvd => hnot ?_⟩
  rw [mem_biUnion]
  exact ⟨j, hj, mem_filter.2 ⟨ht, hdvd⟩⟩

/-- `(2k)!`. -/
def cG (k : ℕ) : ℕ := (2 * k)!

/-- `(2k)!² / k`. -/
def cH (k : ℕ) : ℕ := cG k * (cG k / k)

/-- Slopes of the linear forms. -/
def formA (k p v : ℕ) : ℕ := if v < k then cG k * (cG k / v) * p else cH k

/-- Constant terms of the linear forms. -/
def formB (k p m v : ℕ) : ℕ := if v < k then cG k * (cG k / v) * m + 1 else (cH k * m + 1) / p

/-- `n(t) = (2k)!² (m + p t)`. -/
def cN (k p m t : ℕ) : ℕ := cG k * cG k * m + cG k * cG k * p * t

theorem dvd_cG {k v : ℕ} (hv : 1 ≤ v) (hvk : v ≤ 2 * k) : v ∣ cG k :=
  Nat.dvd_factorial (by omega) hvk

theorem mul_div_cG {k v : ℕ} (hv : 1 ≤ v) (hvk : v ≤ 2 * k) : v * (cG k / v) = cG k :=
  Nat.mul_div_cancel' (dvd_cG hv hvk)

theorem formA_pos {k p v : ℕ} (hp : 0 < p) (hv : 1 ≤ v) (hvk : v ≤ k) : 0 < formA k p v := by
  have hG : 0 < cG k := Nat.factorial_pos _
  have h1 : 0 < cG k / v := Nat.div_pos (Nat.le_of_dvd hG (dvd_cG hv (by omega))) (by omega)
  have h2 : 0 < cG k / k := Nat.div_pos (Nat.le_of_dvd hG (dvd_cG (by omega) (by omega)))
    (by omega)
  unfold formA cH
  split_ifs
  · positivity
  · positivity

theorem exists_m {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : 2 * k < p) :
    ∃ m, p ∣ cH k * m + 1 := by
  have hpG : ¬ p ∣ cG k := fun h => by
    have := (Nat.Prime.dvd_factorial hp).1 h
    omega
  have hcop : Nat.Coprime (cH k) p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpG h
    · exact hpG (h.trans (Nat.div_dvd_of_dvd (dvd_cG (by omega) (by omega))))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime (p - 1) hcop hp.ne_zero
  refine ⟨m, Nat.dvd_of_mod_eq_zero ?_⟩
  rw [Nat.add_mod, hm, Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt hp.one_lt,
    Nat.sub_add_cancel hp.one_lt.le, Nat.mod_self]

section Forms

variable {k p m : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : 2 * k < p) (hm : p ∣ cH k * m + 1)
include hk hp hkp hm

theorem cN_add (t : ℕ) {v : ℕ} (hv : 1 ≤ v) (hvk : v ≤ k) :
    cN k p m t + v = cof k p v * (formA k p v * t + formB k p m v) := by
  unfold cN cof formA formB
  split_ifs with h
  · have hg := mul_div_cG (k := k) hv (by omega)
    generalize cG k / v = g at hg ⊢
    zify at hg ⊢
    linear_combination (-(cG k : ℤ) * p * t - cG k * m) * hg
  · have hvk' : v = k := by omega
    subst hvk'
    obtain ⟨r, hr⟩ := hm
    rw [hr, Nat.mul_div_cancel_left r hp.pos]
    have hg := mul_div_cG (k := v) hk (by omega)
    unfold cH at hr ⊢
    generalize cG v / v = g at hg hr ⊢
    zify at hg hr ⊢
    linear_combination (-(cG v : ℤ) * p * t - cG v * m) * hg + (v : ℤ) * hr

theorem admissible {ℓ : ℕ} (hℓ : ℓ.Prime) {v : ℕ} (hv : 1 ≤ v) (hvk : v ≤ k) :
    (ℓ ∣ formA k p v → ¬ ℓ ∣ formB k p m v) ∧ (¬ ℓ ∣ formA k p v → 2 * k < ℓ) := by
  have hsmall : ℓ ≤ 2 * k → ℓ ∣ cG k := fun h => Nat.dvd_factorial hℓ.pos h
  unfold formA formB
  split_ifs with h
  · refine ⟨fun hA hB => ?_, fun hA => ?_⟩
    · rcases (Nat.Prime.dvd_mul hℓ).1 hA with h1 | h1
      · have h2 : ℓ ∣ cG k * (cG k / v) * m := dvd_mul_of_dvd_left h1 _
        exact hℓ.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 hB))
      · have hℓp : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1
        subst hℓp
        have hg := mul_div_cG (k := k) hv (by omega)
        have hB' : ℓ ∣ cG k * cG k * m + v := by
          have := dvd_mul_of_dvd_right hB v
          rwa [show v * (cG k * (cG k / v) * m + 1) = cG k * cG k * m + v by
            generalize cG k / v = g at hg ⊢
            rw [← hg]; ring] at this
        have hk' : ℓ ∣ cG k * cG k * m + k := by
          have := dvd_mul_of_dvd_right hm k
          have hgk := mul_div_cG (k := k) hk (by omega)
          rwa [show k * (cH k * m + 1) = cG k * cG k * m + k by
            unfold cH
            generalize cG k / k = g at hgk ⊢
            rw [← hgk]; ring] at this
        have hdiff : ℓ ∣ k - v := by
          have := Nat.dvd_sub hk' hB'
          rwa [Nat.add_sub_add_left] at this
        have := Nat.le_of_dvd (by omega) hdiff
        omega
    · by_contra hc
      exact hA (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hsmall (by omega)) _) _)
  · refine ⟨fun hA hB => ?_, fun hA => ?_⟩
    · obtain ⟨r, hr⟩ := hm
      rw [hr, Nat.mul_div_cancel_left r hp.pos] at hB
      have h1 : ℓ ∣ p * r := dvd_mul_of_dvd_right hB p
      rw [← hr] at h1
      have h2 : ℓ ∣ cH k * m := dvd_mul_of_dvd_left hA m
      exact hℓ.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
    · by_contra hc
      exact hA (dvd_mul_of_dvd_left (hsmall (by omega)) _)

end Forms

/-- Arbitrarily large `t` making all the forms prime give arbitrarily large good `n`. -/
theorem good_of_primes {k p m : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hkp : 2 * k < p)
    (hm : p ∣ cH k * m + 1)
    (hprimes : ∀ M, ∃ t, M < t ∧ ∀ v, 1 ≤ v → v ≤ k → (formA k p v * t + formB k p m v).Prime) :
    ∀ M, ∃ n, M ≤ n ∧ ∀ i, 1 ≤ i → i ≤ k →
      ∃ q, q.Prime ∧ cof k p i < q ∧ n + i = cof k p i * q := by
  intro M
  obtain ⟨t, hMt, ht⟩ := hprimes (M + k * p)
  refine ⟨cN k p m t, ?_, fun v hv hvk => ⟨_, ht v hv hvk, ?_, cN_add hk hp hkp hm t hv hvk⟩⟩
  · have h1 : 1 ≤ cG k * cG k * p :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)) hp.ne_zero)
    unfold cN
    nlinarith
  · have hA := formA_pos hp.pos hv hvk
    have hcof : cof k p v ≤ k * p := by
      unfold cof
      split_ifs
      · nlinarith [hp.pos]
      · exact le_rfl
    nlinarith

/-! ### The conditional variants -/

/--
**Bunyakovsky condition**
A condition on polynomials in the Schinzel and Bunyakovsky conjectures.
Holds for nonconstant irreducible polynomial with positive leading coefficient.
-/
def BunyakovskyCondition (f : ℤ[X]) : Prop :=
  1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff

/--
**Schinzel condition**
A condition on sets of polynomials in the Schinzel and Bunyakovsky conjectures.
Holds if for every prime $p$ there exists a natural $n$ such that for every polynomial $f$ in the set, $p$ does not divide $f(n)$.
-/
def SchinzelCondition (fs : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ fs, ¬(p : ℤ) ∣ f.eval (n : ℤ)

-- The binder name `hab` in the statement is kept verbatim from formal-conjectures.
set_option linter.unusedVariables false in
/-- If the prime `k`-tuples conjecture is true, then `∑ σ k n / n!` is irrational. This is proved
in [FLC07]. -/
theorem erdos_252.variants.prime_tuples {k : ℕ} (hk : 4 ≤ k) (hp : ∀ (a : Fin k → ℕ+)
    (b : Fin k → ℕ) (hab : ∀ p, p.Prime → ∃ n, ¬ p ∣ ∏ i, (a i * n + b i)),
    Set.Infinite {n | ∀ i : Fin k, (a i * n + b i).Prime} ) :
    Irrational (erdos_252_sum k) := by
  obtain ⟨p, hp1, hpp⟩ := Nat.exists_infinite_primes (σ k k + 2 * k + 1)
  obtain ⟨m, hm⟩ := exists_m (k := k) (by omega) hpp (by omega)
  refine irrational_of_good (by omega) hpp (by omega)
    (good_of_primes (by omega) hpp (by omega) hm fun M => ?_)
  let a : Fin k → ℕ+ := fun i =>
    ⟨formA k p (i + 1), formA_pos hpp.pos (by omega) (by omega)⟩
  let b : Fin k → ℕ := fun i => formB k p m (i + 1)
  have hab : ∀ ℓ : ℕ, ℓ.Prime → ∃ t, ¬ ℓ ∣ ∏ i, (a i * t + b i) := by
    intro ℓ hℓ
    obtain ⟨t, ht⟩ := exists_forall_not_dvd (univ : Finset (Fin k))
      (fun i => (formA k p (i + 1) : ℤ)) (fun i => (formB k p m (i + 1) : ℤ)) hℓ fun i _ => by
        have h := admissible (k := k) (by omega) hpp (by omega) hm hℓ (v := i + 1)
          (by omega) (by omega)
        rw [card_univ, Fintype.card_fin]
        refine ⟨fun hA hB => h.1 (Int.natCast_dvd_natCast.1 hA) (Int.natCast_dvd_natCast.1 hB),
          fun hA => ?_⟩
        have := h.2 fun h' => hA (Int.natCast_dvd_natCast.2 h')
        omega
    refine ⟨t, fun hdvd => ?_⟩
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 hℓ) _).1 hdvd
    exact ht i (mem_univ _) (by exact_mod_cast hi)
  obtain ⟨t, ht, hMt⟩ := (hp a b hab).exists_gt M
  refine ⟨t, hMt, fun v hv hvk => ?_⟩
  have := ht ⟨v - 1, by omega⟩
  simp only [a, b, PNat.mk_coe] at this
  rwa [show v - 1 + 1 = v by omega] at this

/-- If Schinzel's conjecture is true, then `∑ σ k n / n!` is irrational for all `k`. This is proved
in [ScPu06]. -/
theorem erdos_252.variants.schinzel (hs : ∀ (fs : Finset (Polynomial ℤ)),
    (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    Infinite ↑{n | ∀ f ∈ fs, Prime (Polynomial.eval (↑n) f).natAbs}) :
    ∀ k, Irrational (erdos_252_sum k) := by
  intro k
  rcases (show k ≤ 2 ∨ 3 ≤ k by omega) with hk | hk
  · interval_cases k
    · exact erdos_252.variants.k_eq_zero
    · exact erdos_252.variants.k_eq_one
    · exact erdos_252.variants.k_eq_two
  obtain ⟨p, hp1, hpp⟩ := Nat.exists_infinite_primes (σ k k + 2 * k + 1)
  obtain ⟨m, hm⟩ := exists_m (k := k) (by omega) hpp (by omega)
  refine irrational_of_good (by omega) hpp (by omega)
    (good_of_primes (by omega) hpp (by omega) hm fun M => ?_)
  -- the forms `A x + B` and `A x - B`
  let A : Fin k × Bool → ℤ := fun j => formA k p (j.1 + 1)
  let B : Fin k × Bool → ℤ := fun j =>
    if j.2 then (formB k p m (j.1 + 1) : ℤ) else -(formB k p m (j.1 + 1) : ℤ)
  let lin : Fin k × Bool → ℤ[X] := fun j => C (A j) * X + C (B j)
  have hA0 : ∀ j, A j ≠ 0 := fun j => by
    have := formA_pos (k := k) hpp.pos (v := j.1 + 1) (by omega) (by omega)
    simp only [A]
    omega
  have hadm : ∀ j, ∀ ℓ : ℕ, ℓ.Prime → ((ℓ : ℤ) ∣ A j → ¬ (ℓ : ℤ) ∣ B j) ∧
      (¬ (ℓ : ℤ) ∣ A j → 2 * k < ℓ) := fun j ℓ hℓ => by
    have h := admissible (k := k) (by omega) hpp (by omega) hm hℓ (v := j.1 + 1)
      (by omega) (by omega)
    refine ⟨fun hA hB => h.1 (Int.natCast_dvd_natCast.1 hA) ?_,
      fun hA => h.2 fun h' => hA (Int.natCast_dvd_natCast.2 h')⟩
    simp only [B] at hB
    split_ifs at hB
    · exact Int.natCast_dvd_natCast.1 hB
    · exact Int.natCast_dvd_natCast.1 (dvd_neg.1 hB)
  have hcop : ∀ j, IsRelPrime (B j) (A j) := fun j => by
    have hc : Nat.Coprime (formB k p m (j.1 + 1)) (formA k p (j.1 + 1)) :=
      Nat.coprime_of_dvd fun ℓ hℓ hB hA =>
        (hadm j ℓ hℓ).1 (Int.natCast_dvd_natCast.2 hA) (by
          simp only [B]
          split_ifs
          · exact Int.natCast_dvd_natCast.2 hB
          · exact dvd_neg.2 (Int.natCast_dvd_natCast.2 hB))
    have hc' : IsCoprime (formB k p m (j.1 + 1) : ℤ) (formA k p (j.1 + 1) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 hc
    simp only [A, B]
    split_ifs
    · exact hc'.isRelPrime
    · exact hc'.neg_left.isRelPrime
  set fs := (univ : Finset (Fin k × Bool)).image lin with hfs
  have hBun : ∀ f ∈ fs, BunyakovskyCondition f := by
    intro f hf
    obtain ⟨j, -, rfl⟩ := mem_image.1 hf
    refine ⟨(degree_linear (hA0 j)).ge, irreducible_of_degree_eq_one_of_isRelPrime_coeff
      (degree_linear (hA0 j)) ?_, ?_⟩
    · simp only [lin, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero, mul_zero, zero_add,
        coeff_X_one, coeff_C_succ, mul_one, add_zero]
      exact hcop j
    · rw [leadingCoeff_linear (hA0 j)]
      have := formA_pos (k := k) hpp.pos (v := j.1 + 1) (by omega) (by omega)
      simp only [A]
      omega
  have hSch : SchinzelCondition fs := by
    intro ℓ hℓ
    obtain ⟨t, ht⟩ := exists_forall_not_dvd (univ : Finset (Fin k × Bool)) A B hℓ fun j _ => by
      rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      exact ⟨(hadm j ℓ hℓ).1, fun hA => by have := (hadm j ℓ hℓ).2 hA; omega⟩
    refine ⟨t, fun f hf => ?_⟩
    obtain ⟨j, -, rfl⟩ := mem_image.1 hf
    simpa [lin] using ht j (mem_univ _)
  have hinf := Set.infinite_coe_iff.1 (hs fs hBun hSch)
  obtain ⟨x, hx, hxM⟩ := hinf.exists_notMem_finite (Set.finite_Icc (-(M : ℤ)) M)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxM
  have hval : ∀ j, (lin j).eval x = A j * x + B j := fun j => by simp [lin]
  have hprime : ∀ j, (A j * x + B j).natAbs.Prime := fun j => by
    have := hx (lin j) (mem_image_of_mem _ (mem_univ _))
    rw [hval] at this
    exact Nat.prime_iff.2 this
  rcases hxM with hneg | hpos
  · refine ⟨(-x).toNat, by omega, fun v hv hvk => ?_⟩
    have h := hprime (⟨v - 1, by omega⟩, false)
    have hx' : x = -(((-x).toNat : ℕ) : ℤ) := by omega
    simp only [A, B, show v - 1 + 1 = v by omega, Bool.false_eq_true, ↓reduceIte] at h
    rw [hx', show (formA k p v : ℤ) * -(((-x).toNat : ℕ) : ℤ) + -(formB k p m v : ℤ) =
      -((formA k p v * (-x).toNat + formB k p m v : ℕ) : ℤ) by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast] at h
    exact h
  · refine ⟨x.toNat, by omega, fun v hv hvk => ?_⟩
    have h := hprime (⟨v - 1, by omega⟩, true)
    have hx' : x = ((x.toNat : ℕ) : ℤ) := by omega
    simp only [A, B, show v - 1 + 1 = v by omega, ↓reduceIte] at h
    rw [hx', show (formA k p v : ℤ) * ((x.toNat : ℕ) : ℤ) + (formB k p m v : ℤ) =
      ((formA k p v * x.toNat + formB k p m v : ℕ) : ℤ) by push_cast; ring,
      Int.natAbs_natCast] at h
    exact h

end Erdos252
