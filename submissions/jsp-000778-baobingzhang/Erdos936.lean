import Mathlib

/-!
# Erdős Problem 936: under the abc conjecture, `2^n ± 1` and `n! ± 1` are rarely powerful

Erdős [Er76d, p. 32] asked (https://www.erdosproblems.com/936):

> Are `2^n ± 1` and `n! ± 1` powerful (i.e. if `p ∣ m` then `p² ∣ m`) for only finitely many `n`?

The problem is open. Cushing and Pascoe [CuPa16] showed that the answer to the second question
(`n! ± 1`) is yes if the abc conjecture holds, and CrowdMath [Cr20] showed the same for the first
question (`2^n ± 1`). This file proves both conditional answers, for all four sequences:

* `Erdos936.erdos_936.variants.two_pow_add_one_of_abc (habc : ABC.ABCConjecture) :
    EventuallyNotPowerful (2 ^ · + 1)`
* `Erdos936.erdos_936.variants.two_pow_sub_one_of_abc (habc : ABC.ABCConjecture) :
    EventuallyNotPowerful (2 ^ · - 1)`
* `Erdos936.erdos_936.variants.factorial_add_one_of_abc (habc : ABC.ABCConjecture) :
    EventuallyNotPowerful (·! + 1)`
* `Erdos936.erdos_936.variants.factorial_sub_one_of_abc (habc : ABC.ABCConjecture) :
    EventuallyNotPowerful (·! - 1)`
* `Erdos936.erdos_936_of_abc (habc : ABC.ABCConjecture)`: the sets `{n | (2 ^ n + 1).Powerful}`,
  `{n | (2 ^ n - 1).Powerful}`, `{n | (n ! + 1).Powerful}` and `{n | ((n)! - 1).Powerful}` are all
  finite.

## Definitions and faithfulness

* `Nat.Full` and `Nat.Powerful` are copied verbatim from Google DeepMind's formal-conjectures
  project (`FormalConjecturesForMathlib/Data/Nat/Full.lean`, Apache-2.0): `n` is powerful when
  `p ^ 2 ∣ n` for every prime factor `p` of `n`. This is the definition on the problem page.
  (`0` and `1` are powerful under it; this does not affect any finiteness statement.)
* `Erdos936.EventuallyNotPowerful` is copied verbatim from formal-conjectures
  (`FormalConjectures/ErdosProblems/936.lean`). There the four open variants
  `erdos_936.variants.two_pow_add_one`, `two_pow_sub_one`, `factorial_add_one` and
  `factorial_sub_one` read `answer(…) ↔ EventuallyNotPowerful (…)` with the answer left open; the
  four theorems above prove exactly these right-hand sides under the abc conjecture, i.e. the
  answer "yes" in each case, conditionally. The suffix `_of_abc` marks the added hypothesis.
  `eventuallyNotPowerful_iff_finite` shows that `EventuallyNotPowerful a` says precisely that
  `a n` is powerful for only finitely many `n`.
* Subtraction in `ℕ` is truncated, but `2 ^ n ≥ 1` and `n ! ≥ 1` for every `n`, so `2 ^ n - 1` and
  `n ! - 1` are the integers `2^n - 1` and `n! - 1` for every `n`.
* `ABC.radical` is copied verbatim from formal-conjectures (`FormalConjectures/Wikipedia/ABC.lean`).
  `ABC.ABCConjecture` is the statement of the theorem `ABC.abc` of that file (category "research
  open"), written as a proposition: for every real `ε > 0` only finitely many triples `(a, b, c)` of
  pairwise coprime positive integers with `a + b = c` satisfy `rad(abc)^(1+ε) < c`. The only change
  is that the binders `(ε : ℝ) (hε : 0 < ε)` are written `∀ (ε : ℝ), 0 < ε → …`, which is the same
  proposition. The abc conjecture is open; it appears only as the explicit hypothesis `habc` of the
  main theorems and is never assumed globally.

## Proof

* **Radical bounds.** If `x ≠ 0` is powerful then `rad(x)² ≤ x` (`ABC.radical_sq_le`), because
  `x = ∏_{p ∣ x} p^(v_p(x))` with every `v_p(x) ≥ 2`. Also `rad(ab) ≤ rad(a) rad(b)`
  (`ABC.radical_mul_le`), `rad(2^n) = 2` for `n ≥ 1` (`ABC.radical_two_pow`), and
  `rad(n!) ≤ 4^n` (`ABC.radical_factorial_le`), because `rad(n!)` divides the primorial of `n`,
  which is at most `4^n` by Mathlib.
* **Using abc** (`finite_setOf_radical_lt`). The triples `(a, 1, a + 1)` are pairwise coprime, and
  `r⁴ < c³` gives `r^(1 + 1/3) < c`. So the abc conjecture with `ε = 1/3` shows that only finitely
  many `a > 0` satisfy `rad(a · 1 · (a + 1))⁴ < (a + 1)³`.
* **The inequality** (`pow_four_lt`). If `r ≤ R s`, `s² ≤ c` and `R⁴ < c`, then
  `r⁴ ≤ R⁴ (s²)² ≤ R⁴ c² < c³`.
* **The four sequences.** Take `a = 2^n`, `2^n - 1`, `n!` or `n! - 1`, so that the number in
  question is `a + 1` or `a`, and the other one of `a`, `a + 1` is `2^n` or `n!`. If the number in
  question is powerful, put `s` = its radical and `R = 2` (for `2^n`) or `R = 4^n` (for `n!`).
  Then `rad(a(a + 1)) ≤ R s`, `s² ≤ a + 1`, and `R⁴ < a + 1` holds for `n ≥ 5` (`16 < 2^n`),
  respectively for all large `n` (`256^n < n!` eventually, Mathlib's
  `Nat.eventually_pow_lt_factorial_sub`). So `a` lies in the finite set above. Since `n ≤ a + 1`
  in all four cases, this can happen for only finitely many `n` (`eventually_notMem`).

These are the standard deductions from the abc conjecture; the details differ from [CuPa16] and
[Cr20].

## What is not proved here

* The unconditional problem, which is open.
* The more general statements of the sources: [CuPa16] show under abc that for every fixed `k ≥ 0`
  only finitely many `n` and powerful `x` satisfy `|x - n!| ≤ k`, and [Cr20] treat sequences of the
  form `k^n + r`. Only the four sequences in Erdős's question are formalized.

## References

* [Er76d] Erdős, P., as cited on erdosproblems.com/936 (p. 32).
* [CuPa16] Cushing, D. and Pascoe, J. E., _Powerful numbers and the ABC-conjecture_.
  arXiv:1611.01192 (2016).
* [Cr20] CrowdMath, _Applications of the abc conjecture to powerful numbers_. arXiv:2005.07321
  (2020).
* [erdosproblems.com/936](https://www.erdosproblems.com/936)
-/

namespace Nat

-- Copied verbatim from formal-conjectures, `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
/--
A natural number $n$ is said to be $k$-full (or $k$-powerful) if for every prime factor $p$ of $n$,
the $k$-th power $p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

-- Copied verbatim from formal-conjectures, `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
/--
A [Powerful number](https://en.wikipedia.org/wiki/Powerful_number) is a natural number $n$ where
for every prime divisor $p$, $p^2$ divides $n$.
Powerful numbers are also known as "squareful", "square-full", or "$2$-full".
-/
abbrev Powerful : ℕ → Prop := (2).Full

end Nat

namespace ABC

-- Copied verbatim from formal-conjectures, `FormalConjectures/Wikipedia/ABC.lean`.
/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

-- The statement of `ABC.abc` in formal-conjectures, `FormalConjectures/Wikipedia/ABC.lean`, as a
-- proposition (binders `(ε : ℝ) (hε : 0 < ε)` written as `∀ (ε : ℝ), 0 < ε → …`).
/--
The abc conjecture: for every positive real number `ε`, there exist only finitely many triples
`(a, b, c)` of coprime positive integers, with `a + b = c`, such that `c > rad(abc)^(1+ε)`.
-/
def ABCConjecture : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

/-- `rad(ab) ≤ rad(a) rad(b)` for nonzero `a` and `b`. -/
theorem radical_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    radical (a * b) ≤ radical a * radical b := by
  unfold radical
  rw [Nat.primeFactors_mul ha hb, ← Finset.prod_union_inter]
  exact Nat.le_mul_of_pos_right _
    (Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.1 hp).1).pos)

/-- A nonzero powerful number `x` satisfies `rad(x)² ≤ x`. -/
theorem radical_sq_le {x : ℕ} (hx : x ≠ 0) (hp : x.Powerful) : radical x ^ 2 ≤ x := by
  unfold radical
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hx]
  rw [Finsupp.prod, Nat.support_factorization, ← Finset.prod_pow]
  refine Finset.prod_le_prod fun p hpx => ?_
  have hpp := Nat.prime_of_mem_primeFactors hpx
  exact Nat.pow_le_pow_right hpp.pos ((hpp.pow_dvd_iff_le_factorization hx).1 (hp p hpx))

/-- `rad(2^n) = 2` for `n ≥ 1`. -/
theorem radical_two_pow {n : ℕ} (hn : n ≠ 0) : radical (2 ^ n) = 2 := by
  rw [radical, Nat.primeFactors_prime_pow hn Nat.prime_two, Finset.prod_singleton, id]

/-- `rad(n!) ≤ 4^n`: `rad(n!)` divides the primorial of `n`. -/
theorem radical_factorial_le (n : ℕ) : radical n.factorial ≤ 4 ^ n := by
  refine le_trans (Nat.le_of_dvd (primorial_pos n) ?_) (primorial_le_four_pow n)
  unfold radical primorial
  refine Finset.prod_dvd_prod_of_subset _ _ id fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (hpp.dvd_factorial.1 (Nat.dvd_of_mem_primeFactors hp)), hpp⟩

end ABC

open Filter Nat

namespace Erdos936

open ABC

/-- If `r ≤ R s`, `s² ≤ c` and `R⁴ < c`, then `r⁴ < c³`. -/
theorem pow_four_lt {r R s c : ℕ} (hr : r ≤ R * s) (hs : s ^ 2 ≤ c) (hR : R ^ 4 < c) :
    r ^ 4 < c ^ 3 := by
  have hc : 0 < c ^ 2 := pow_pos (lt_of_le_of_lt (Nat.zero_le _) hR) 2
  calc r ^ 4 ≤ (R * s) ^ 4 := Nat.pow_le_pow_left hr 4
    _ = R ^ 4 * (s ^ 2) ^ 2 := by ring
    _ ≤ R ^ 4 * c ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
    _ < c * c ^ 2 := Nat.mul_lt_mul_of_pos_right hR hc
    _ = c ^ 3 := by ring

/-- `r⁴ < c³` implies `r^(1 + 1/3) < c` in `ℝ`. -/
theorem rpow_lt_of_pow_four_lt {r c : ℕ} (h : r ^ 4 < c ^ 3) :
    (r : ℝ) ^ (1 + (1 / 3 : ℝ)) < c := by
  have h' : ((r : ℝ) ^ (4 : ℕ)) < (c : ℝ) ^ (3 : ℕ) := by exact_mod_cast h
  have e1 : (r : ℝ) ^ (1 + (1 / 3 : ℝ)) = ((r : ℝ) ^ (4 : ℕ)) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg r)]; norm_num
  have e2 : (c : ℝ) = ((c : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg c)]; norm_num
  rw [e1]
  conv_rhs => rw [e2]
  exact Real.rpow_lt_rpow (by positivity) h' (by norm_num)

/-- The triple `(a, 1, a + 1)` is pairwise coprime. -/
theorem pairwise_coprime (a : ℕ) : ({a, 1, a + 1} : Set ℕ).Pairwise Nat.Coprime := by
  have h : a.Coprime (a + 1) := by simp
  rw [Set.pairwise_insert_of_symm, Set.pairwise_insert_of_symm]
  refine ⟨⟨Set.pairwise_singleton _ _, fun b hb _ => ?_⟩, fun b hb _ => ?_⟩
  · simp only [Set.mem_singleton_iff] at hb
    subst hb
    exact Nat.coprime_one_left _
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact h

/-- Under the abc conjecture (with `ε = 1/3`, applied to the triples `(a, 1, a + 1)`), only
finitely many `a > 0` satisfy `rad(a · 1 · (a + 1))⁴ < (a + 1)³`. -/
theorem finite_setOf_radical_lt (habc : ABCConjecture) :
    {a : ℕ | 0 < a ∧ radical (a * 1 * (a + 1)) ^ 4 < (a + 1) ^ 3}.Finite := by
  have hE := habc (1 / 3) (by norm_num)
  refine (hE.preimage (f := fun a : ℕ => (a, 1, a + 1)) ?_).subset ?_
  · intro a _ b _ hab
    simpa using hab
  · rintro a ⟨ha, hr⟩
    exact ⟨ha, Nat.one_pos, Nat.succ_pos a, pairwise_coprime a, rfl,
      rpow_lt_of_pow_four_lt hr⟩

/-- If `n ≤ f n + 1` for all `n`, then `f n` eventually avoids any finite set. -/
theorem eventually_notMem {T : Set ℕ} (hT : T.Finite) {f : ℕ → ℕ} (hf : ∀ n, n ≤ f n + 1) :
    ∀ᶠ n in atTop, f n ∉ T := by
  obtain ⟨B, hB⟩ := hT.bddAbove
  filter_upwards [eventually_gt_atTop (B + 1)] with n hn hmem
  have h1 := hB hmem
  have h2 := hf n
  omega

-- Copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/936.lean`.
/--
The predicate that `a n` is only powerful for finitely many `n`.
-/
def EventuallyNotPowerful (a : ℕ → ℕ) : Prop := atTop.Eventually (fun n => ¬ (a n).Powerful)

/-- `EventuallyNotPowerful a` holds exactly when `a n` is powerful for only finitely many `n`. -/
theorem eventuallyNotPowerful_iff_finite (a : ℕ → ℕ) :
    EventuallyNotPowerful a ↔ {n | (a n).Powerful}.Finite := by
  rw [EventuallyNotPowerful, ← Nat.cofinite_eq_atTop, eventually_cofinite]
  simp

/-- Assuming the abc conjecture, `2^n + 1` is powerful for only finitely many `n` [Cr20]. -/
theorem erdos_936.variants.two_pow_add_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (2 ^ · + 1) := by
  have hT := eventually_notMem (finite_setOf_radical_lt habc) (f := fun n => 2 ^ n)
    (fun n => (Nat.lt_two_pow_self (n := n)).le.trans (Nat.le_succ _))
  unfold EventuallyNotPowerful
  filter_upwards [hT, eventually_ge_atTop 4] with n hn h4 hpow
  apply hn
  refine ⟨by positivity, pow_four_lt (R := 2) (s := radical (2 ^ n + 1)) ?_
    (radical_sq_le (by positivity) hpow) ?_⟩
  · rw [mul_one]
    refine (radical_mul_le (by positivity) (by positivity)).trans ?_
    rw [radical_two_pow (by omega)]
  · calc 2 ^ 4 < 2 ^ 4 + 1 := by norm_num
      _ ≤ 2 ^ n + 1 := by gcongr

/-- Assuming the abc conjecture, `2^n - 1` is powerful for only finitely many `n` [Cr20]. -/
theorem erdos_936.variants.two_pow_sub_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (2 ^ · - 1) := by
  have hT := eventually_notMem (finite_setOf_radical_lt habc) (f := fun n => 2 ^ n - 1)
    (fun n => by have := Nat.lt_two_pow_self (n := n); omega)
  unfold EventuallyNotPowerful
  filter_upwards [hT, eventually_ge_atTop 5] with n hn h5 hpow
  apply hn
  have h32 : 32 ≤ 2 ^ n :=
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
  have hsub : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  show 0 < 2 ^ n - 1 ∧ radical ((2 ^ n - 1) * 1 * (2 ^ n - 1 + 1)) ^ 4 < (2 ^ n - 1 + 1) ^ 3
  rw [hsub]
  refine ⟨by omega, pow_four_lt (R := 2) (s := radical (2 ^ n - 1)) ?_
    ((radical_sq_le (by omega) hpow).trans (Nat.sub_le _ _)) (by omega)⟩
  rw [mul_one]
  refine (radical_mul_le (by omega) (by positivity)).trans ?_
  rw [radical_two_pow (by omega), mul_comm]

/-- Assuming the abc conjecture, `n! + 1` is powerful for only finitely many `n` [CuPa16]. -/
theorem erdos_936.variants.factorial_add_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (·! + 1) := by
  have hT := eventually_notMem (finite_setOf_radical_lt habc) (f := fun n => n !)
    (fun n => (Nat.self_le_factorial n).trans (Nat.le_succ _))
  unfold EventuallyNotPowerful
  filter_upwards [hT, Nat.eventually_pow_lt_factorial_sub 256 0] with n hn hfac hpow
  rw [Nat.sub_zero] at hfac
  apply hn
  show 0 < n ! ∧ radical (n ! * 1 * (n ! + 1)) ^ 4 < (n ! + 1) ^ 3
  refine ⟨Nat.factorial_pos n, pow_four_lt (R := 4 ^ n) (s := radical (n ! + 1)) ?_
    (radical_sq_le (by positivity) hpow) ?_⟩
  · rw [mul_one]
    exact (radical_mul_le (Nat.factorial_ne_zero n) (by positivity)).trans
      (Nat.mul_le_mul_right _ (radical_factorial_le n))
  · calc (4 ^ n) ^ 4 = 256 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ < n ! := hfac
      _ < n ! + 1 := Nat.lt_succ_self _

/-- Assuming the abc conjecture, `n! - 1` is powerful for only finitely many `n` [CuPa16]. -/
theorem erdos_936.variants.factorial_sub_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (·! - 1) := by
  have hT := eventually_notMem (finite_setOf_radical_lt habc) (f := fun n => (n)! - 1)
    (fun n => by have := Nat.self_le_factorial n; have := Nat.factorial_pos n; omega)
  unfold EventuallyNotPowerful
  filter_upwards [hT, Nat.eventually_pow_lt_factorial_sub 256 0] with n hn hfac hpow
  rw [Nat.sub_zero] at hfac
  apply hn
  have h1 : 1 ≤ 256 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hsub : (n)! - 1 + 1 = n ! := by omega
  show 0 < (n)! - 1 ∧ radical (((n)! - 1) * 1 * ((n)! - 1 + 1)) ^ 4 < ((n)! - 1 + 1) ^ 3
  rw [hsub]
  refine ⟨by omega, pow_four_lt (R := 4 ^ n) (s := radical ((n)! - 1)) ?_
    ((radical_sq_le (by omega) hpow).trans (Nat.sub_le _ _)) ?_⟩
  · rw [mul_one, mul_comm (4 ^ n)]
    exact (radical_mul_le (by omega) (Nat.factorial_ne_zero n)).trans
      (Nat.mul_le_mul_left _ (radical_factorial_le n))
  · calc (4 ^ n) ^ 4 = 256 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ < n ! := hfac

/-- **Erdős Problem 936, conditionally on the abc conjecture.** Each of `2^n + 1`, `2^n - 1`,
`n! + 1` and `n! - 1` is powerful for only finitely many `n` ([Cr20] for `2^n ± 1`, [CuPa16] for
`n! ± 1`). -/
theorem erdos_936_of_abc (habc : ABCConjecture) :
    {n : ℕ | (2 ^ n + 1).Powerful}.Finite ∧ {n : ℕ | (2 ^ n - 1).Powerful}.Finite ∧
      {n : ℕ | (n ! + 1).Powerful}.Finite ∧ {n : ℕ | ((n)! - 1).Powerful}.Finite :=
  ⟨(eventuallyNotPowerful_iff_finite _).1 (erdos_936.variants.two_pow_add_one_of_abc habc),
    (eventuallyNotPowerful_iff_finite _).1 (erdos_936.variants.two_pow_sub_one_of_abc habc),
    (eventuallyNotPowerful_iff_finite _).1 (erdos_936.variants.factorial_add_one_of_abc habc),
    (eventuallyNotPowerful_iff_finite _).1 (erdos_936.variants.factorial_sub_one_of_abc habc)⟩

end Erdos936
