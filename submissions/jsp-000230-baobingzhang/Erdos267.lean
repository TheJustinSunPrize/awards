import Mathlib

/-!
# Erdős Problem 267 for ratio `c ≥ 2` (Badea)

Let `F_n` be the Fibonacci numbers and `n_1 < n_2 < ⋯` with `n_{k+1} / n_k ≥ c > 1`. Erdős asked
whether `∑ 1 / F_{n_k}` must be irrational. Badea proved this for `c ≥ 2`, via his criterion
(Badea 1987): if `(a_k)` are positive integers with `a_{k+1} > a_k² - a_k + 1` for all sufficiently
large `k`, then `∑ 1 / a_k` is irrational.

Main results:
* `badea_criterion`: Badea's criterion, including summability of the series.
* `erdos_267.variants.two_le`: the main statement of Erdős Problem 267 restricted to `c ≥ 2`.
* `erdos_267.variants.specialization_pow_two`: `∑ 1 / F_{2^k}` is irrational (Good, Bicknell and
  Hoggatt), as a corollary.

The statement shapes of `erdos_267.variants.two_le` and `erdos_267.variants.specialization_pow_two`
are copied from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/267.lean`, Apache-2.0); the former replaces `c > 1` by `c ≥ 2`.

Proof of the criterion. Write `r_N = ∑_{k ≥ N} 1 / a_k`. From `a_{k+1} - 1 > a_k (a_k - 1)` we get
`1 / a_k + 1 / (a_{k+1} - 1) < 1 / (a_k - 1)`, and telescoping gives `r_N < 1 / (a_N - 1)`. If the
sum were `p / q`, then `P_N = q · (∏_{k < N} a_k) · r_N` would be positive integers with
`P_{N+1} = a_N P_N - q ∏_{k < N} a_k < P_N`, which is impossible.
-/

namespace Erdos267

open Finset Filter

/-! ### Badea's criterion -/

/-- The telescoping step: if `x ≥ 2` and `y ≥ x² - x + 2`, then `1/x + 1/(y-1) < 1/(x-1)`. -/
theorem one_div_add_one_div_sub_one_lt {x y : ℝ} (hx : 2 ≤ x) (hy : x ^ 2 - x + 2 ≤ y) :
    1 / x + 1 / (y - 1) < 1 / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hy1 : 0 < y - 1 := by nlinarith
  rw [div_add_div _ _ hx0.ne' hy1.ne', div_lt_div_iff₀ (mul_pos hx0 hy1) hx1]
  nlinarith

/-- The growth condition in `ℕ` gives the corresponding real inequality. -/
theorem cast_step {u v : ℕ} (h : u ^ 2 - u + 1 < v) : (u : ℝ) ^ 2 - u + 2 ≤ v := by
  have h2 : u ≤ u ^ 2 := Nat.le_self_pow two_ne_zero u
  have h3 : u ^ 2 + 2 ≤ v + u := by omega
  have h4 : ((u ^ 2 + 2 : ℕ) : ℝ) ≤ (v + u : ℕ) := by exact_mod_cast h3
  push_cast at h4
  linarith

section Real

variable {x : ℕ → ℝ} (hx : ∀ k, 2 ≤ x k) (hstep : ∀ k, x k ^ 2 - x k + 2 ≤ x (k + 1))
include hx hstep

theorem sum_range_add_le (m : ℕ) : ∑ k ∈ range m, 1 / x k + 1 / (x m - 1) ≤ 1 / (x 0 - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := one_div_add_one_div_sub_one_lt (hx m) (hstep m)
    rw [sum_range_succ]
    linarith

omit hstep in
theorem one_div_nonneg' (k : ℕ) : 0 ≤ 1 / x k := by
  have := hx k
  positivity

theorem sum_range_le (m : ℕ) : ∑ k ∈ range m, 1 / x k ≤ 1 / (x 0 - 1) := by
  have h1 := sum_range_add_le hx hstep m
  have h2 : 0 ≤ 1 / (x m - 1) := by
    have := hx m
    exact div_nonneg zero_le_one (by linarith)
  linarith

theorem summable_one_div : Summable fun k => 1 / x k :=
  summable_of_sum_range_le (one_div_nonneg' hx) (sum_range_le hx hstep)

/-- The tail bound `∑ 1 / x_k < 1 / (x_0 - 1)`. -/
theorem tsum_one_div_lt : ∑' k, 1 / x k < 1 / (x 0 - 1) := by
  have h1 : ∑' k, 1 / x (k + 1) ≤ 1 / (x 1 - 1) :=
    Real.tsum_le_of_sum_range_le (one_div_nonneg' (x := fun k => x (k + 1)) fun k => hx _)
      (sum_range_le (x := fun k => x (k + 1)) (fun k => hx _) fun k => hstep _)
  have h2 := one_div_add_one_div_sub_one_lt (hx 0) (hstep 0)
  rw [(summable_one_div hx hstep).tsum_eq_zero_add]
  simp only [zero_add] at h2 ⊢
  linarith

end Real

/-- Badea's criterion when the growth condition holds from the start and all terms are `≥ 2`. -/
theorem irrational_tsum_of_forall {a : ℕ → ℕ} (ha : ∀ k, 2 ≤ a k)
    (hstep : ∀ k, a k ^ 2 - a k + 1 < a (k + 1)) : Irrational (∑' k, 1 / (a k : ℝ)) := by
  -- the real sequence shifted by `N`
  have hxN (N : ℕ) : ∀ k, (2 : ℝ) ≤ a (k + N) := fun k => by exact_mod_cast ha _
  have hstepN (N : ℕ) : ∀ k, (a (k + N) : ℝ) ^ 2 - a (k + N) + 2 ≤ a (k + 1 + N) := fun k => by
    rw [add_right_comm]
    exact cast_step (hstep _)
  -- the tails `T N = ∑_{k ≥ N} 1 / a_k`
  set T : ℕ → ℝ := fun N => ∑' k, 1 / (a (k + N) : ℝ)
  have hTsucc (N : ℕ) : T N = 1 / a N + T (N + 1) := by
    simp only [T]
    rw [(summable_one_div (x := fun k => (a (k + N) : ℝ)) (hxN N) (hstepN N)).tsum_eq_zero_add]
    simp only [zero_add, add_assoc, add_comm 1 N]
  have hTpos (N : ℕ) : 0 < T N :=
    (summable_one_div (x := fun k => (a (k + N) : ℝ)) (hxN N) (hstepN N)).tsum_pos
      (one_div_nonneg' (x := fun k => (a (k + N) : ℝ)) (hxN N)) 0
      (by have := hxN N 0; positivity)
  have hTlt (N : ℕ) : T N < 1 / (a N - 1) := by
    show ∑' k, 1 / (a (k + N) : ℝ) < _
    simpa only [zero_add] using tsum_one_div_lt (x := fun k => (a (k + N) : ℝ)) (hxN N) (hstepN N)
  rintro ⟨r, hr⟩
  -- `D N = q ∏_{k < N} a_k` and `P N = D N * T N`
  set D : ℕ → ℝ := fun N => r.den * ∏ k ∈ range N, (a k : ℝ)
  have hDpos (N : ℕ) : 0 < D N := by
    have : ∀ k ∈ range N, (0 : ℝ) < a k := fun k _ => by
      have := ha k
      positivity
    exact mul_pos (by exact_mod_cast r.den_pos) (prod_pos this)
  have hP_succ (N : ℕ) : D (N + 1) * T (N + 1) = a N * (D N * T N) - D N := by
    have ha0 : (a N : ℝ) ≠ 0 := by
      have := ha N
      positivity
    simp only [D, prod_range_succ]
    rw [hTsucc N]
    field_simp
    ring
  have hP_lt (N : ℕ) : D (N + 1) * T (N + 1) < D N * T N := by
    have ha1 : (0 : ℝ) < a N - 1 := by
      have : (2 : ℝ) ≤ a N := by exact_mod_cast ha N
      linarith
    have h := hTlt N
    rw [lt_div_iff₀ ha1] at h
    have := hDpos N
    rw [hP_succ]
    nlinarith
  have hP_int (N : ℕ) : ∃ z : ℤ, (z : ℝ) = D N * T N := by
    induction N with
    | zero =>
      refine ⟨r.num, ?_⟩
      have hr0 : T 0 = r := by simp only [T, add_zero]; exact hr.symm
      have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
      simp only [D, prod_range_zero, mul_one, hr0, Rat.cast_def]
      field_simp
    | succ N ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨a N * z - r.den * ∏ k ∈ range N, (a k : ℤ), ?_⟩
      rw [hP_succ, ← hz]
      push_cast
      rfl
  choose z hz using hP_int
  have hzdec (N : ℕ) : z (N + 1) < z N := by
    have := hP_lt N
    rw [← hz, ← hz] at this
    exact_mod_cast this
  have hzpos (N : ℕ) : 0 < z N := by
    have : (0 : ℝ) < z N := by
      rw [hz]
      exact mul_pos (hDpos N) (hTpos N)
    exact_mod_cast this
  have hzle (N : ℕ) : z N + N ≤ z 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      have := hzdec N
      push_cast
      omega
  have h1 := hzle (z 0).toNat
  have h2 := hzpos (z 0).toNat
  omega

/-- **Badea's criterion** (Badea 1987). If `a_{k+1} > a_k² - a_k + 1` for all sufficiently large
`k`, then `∑ 1 / a_k` converges to an irrational number.

The subtraction `a k ^ 2 - a k` in `ℕ` never truncates, since `a k ≤ a k ^ 2`. Positivity of the
`a_k` is not needed as a hypothesis: the growth condition forces `a_k ≥ 2` eventually, and finitely
many terms `a_k = 0` (with `1 / 0 = 0`) only change the sum by a rational number. So this is
a slight generalisation of the statement for sequences of positive integers. -/
theorem badea_criterion (a : ℕ → ℕ) (h : ∀ᶠ k in atTop, a k ^ 2 - a k + 1 < a (k + 1)) :
    Summable (fun k => 1 / (a k : ℝ)) ∧ Irrational (∑' k, 1 / (a k : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hb2 : ∀ k, 2 ≤ a (k + (N + 1)) := fun k => by
    have := hN (k + N) (by omega)
    rw [show k + (N + 1) = k + N + 1 by omega]
    omega
  have hbstep : ∀ k, a (k + (N + 1)) ^ 2 - a (k + (N + 1)) + 1 < a (k + 1 + (N + 1)) := fun k => by
    rw [show k + 1 + (N + 1) = k + (N + 1) + 1 by omega]
    exact hN _ (by omega)
  have hsb : Summable fun k => 1 / (a (k + (N + 1)) : ℝ) :=
    summable_one_div (x := fun k => (a (k + (N + 1)) : ℝ)) (fun k => by exact_mod_cast hb2 k)
      fun k => cast_step (hbstep k)
  have hs : Summable fun k => 1 / (a k : ℝ) :=
    (summable_nat_add_iff (f := fun k => 1 / (a k : ℝ)) (N + 1)).1 hsb
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add (N + 1)]
  have := (irrational_tsum_of_forall hb2 hbstep).ratCast_add
    (∑ i ∈ range (N + 1), 1 / (a i : ℚ))
  push_cast at this
  exact this

/-! ### Fibonacci numbers -/

/-- `F_{2m} > F_m² - F_m + 1` for `m ≥ 2`, since `F_{2m} = F_m² + 2 F_m F_{m-1}`. -/
theorem fib_sq_sub_add_one_lt_fib_two_mul {m : ℕ} (hm : 2 ≤ m) :
    Nat.fib m ^ 2 - Nat.fib m + 1 < Nat.fib (2 * m) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have h1 := Nat.fib_add (j + 2) (j + 1)
  have h2 : Nat.fib (j + 2 + 1) = Nat.fib (j + 1) + Nat.fib (j + 2) := Nat.fib_add_two
  rw [show 2 * (j + 2) = j + 2 + (j + 1) + 1 by ring, h1, h2]
  have hA : 0 < Nat.fib (j + 2) := Nat.fib_pos.2 (by omega)
  have hB : 0 < Nat.fib (j + 1) := Nat.fib_pos.2 (by omega)
  have hAB : 0 < Nat.fib (j + 2) * Nat.fib (j + 1) := Nat.mul_pos hA hB
  have hA2 : Nat.fib (j + 2) ≤ Nat.fib (j + 2) ^ 2 := Nat.le_self_pow two_ne_zero _
  have : Nat.fib (j + 2) ^ 2 <
      Nat.fib (j + 2) * Nat.fib (j + 1) +
        (Nat.fib (j + 1) + Nat.fib (j + 2)) * Nat.fib (j + 1 + 1) := by
    nlinarith
  omega

/-- If `n_{k+1} / n_k ≥ c ≥ 2` for all `k`, then `a_k = F_{n_k}` satisfies Badea's growth
condition for all `k ≥ 1`. -/
theorem eventually_fib_step {n : ℕ → ℕ} {c : ℚ} (hc : 2 ≤ c) (hratio : ∀ k, c ≤ n (k + 1) / n k) :
    ∀ᶠ k in atTop, Nat.fib (n k) ^ 2 - Nat.fib (n k) + 1 < Nat.fib (n (k + 1)) := by
  have hn0 (k : ℕ) : 0 < n k := by
    by_contra h0
    have h := hratio k
    simp only [show n k = 0 by omega, Nat.cast_zero, div_zero] at h
    linarith
  have hdouble (k : ℕ) : 2 * n k ≤ n (k + 1) := by
    have hpos : (0 : ℚ) < n k := by exact_mod_cast hn0 k
    have h := hratio k
    rw [le_div_iff₀ hpos] at h
    have : ((2 * n k : ℕ) : ℚ) ≤ n (k + 1) := by
      push_cast
      nlinarith
    exact_mod_cast this
  rw [eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  have h2 : 2 ≤ n k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := hdouble j
    have := hn0 j
    omega
  calc Nat.fib (n k) ^ 2 - Nat.fib (n k) + 1 < Nat.fib (2 * n k) :=
        fib_sq_sub_add_one_lt_fib_two_mul h2
    _ ≤ Nat.fib (n (k + 1)) := Nat.fib_mono (hdouble k)

/-! ### Erdős Problem 267 for `c ≥ 2` -/

/-- The series in `erdos_267.variants.two_le` converges, so its `tsum` is the actual sum. -/
theorem summable_of_two_le : ∀ᵉ (n : ℕ → ℕ) (c ≥ (2 : ℚ)), (∀ k, c ≤ n (k+1) / n k) →
    Summable (fun k => (1 : ℝ) / (Nat.fib <| n k)) := by
  intro n c hc hratio
  exact (badea_criterion _ (eventually_fib_step hc hratio)).1

/--
Let $F_1=F_2=1$ and $F_{n+1} = F_n + F_{n-1}$ be the Fibonacci sequence.
Let $n_1 < n_2 < \dots$ be an infinite sequence with $\frac{n_{k+1}}{n_k} \ge c \ge 2$. Then
$\sum_k \frac 1 {F_{n_k}}$ is irrational (Badea).

This is the main statement `erdos_267` of formal-conjectures with `c > 1` replaced by `c ≥ 2`
(and `answer(True) ↔` removed, since the case `1 < c < 2` is open).
-/
theorem erdos_267.variants.two_le : ∀ᵉ (n : ℕ → ℕ) (c ≥ (2 : ℚ)), StrictMono n →
    (∀ k, c ≤ n (k+1) / n k) → Irrational (∑' k, 1 / (Nat.fib <| n k)) := by
  intro n c hc _ hratio
  exact (badea_criterion _ (eventually_fib_step hc hratio)).2

theorem two_le_pow_two_ratio (k : ℕ) : (2 : ℚ) ≤ ((2 ^ (k + 1) : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  have : ((2 ^ (k + 1) : ℕ) : ℚ) / ((2 ^ k : ℕ) : ℚ) = 2 := by
    push_cast
    rw [pow_succ]
    field_simp
  exact this.ge

/-- The series in `erdos_267.variants.specialization_pow_two` converges. -/
theorem summable_pow_two : Summable fun k => (1 : ℝ) / (Nat.fib <| 2^k) :=
  summable_of_two_le (fun k => 2 ^ k) 2 le_rfl two_le_pow_two_ratio

/--
Good [Go74] and Bicknell and Hoggatt [BiHo76] have shown that $\sum_n \frac 1 {F_{2^n}}$ is
irrational. Here it follows from the `c = 2` case.
-/
theorem erdos_267.variants.specialization_pow_two :
    Irrational <| ∑' k, 1 / (Nat.fib <| 2^k) :=
  erdos_267.variants.two_le (fun k => 2 ^ k) 2 le_rfl (pow_right_strictMono₀ one_lt_two)
    two_le_pow_two_ratio

end Erdos267
