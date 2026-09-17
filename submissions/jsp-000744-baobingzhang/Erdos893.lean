import Mathlib

/-!
# Erdős Problem 893: the doubling ratios `f(2n)/f(n)` are unbounded

Let `τ(n)` be the number of divisors of `n` and `f(n) = ∑_{1 ≤ k ≤ n} τ(2^k - 1)`. Erdős [Er98]
asked whether `f(2n)/f(n)` tends to a limit. Kovač and Luca [KoLu25, Theorem 1] proved that
`limsup_{n → ∞} f(2n)/f(n) = ∞`, so there is no finite limit. This file proves that theorem:

* `Erdos893.erdos_893.variants.unbounded :
    ¬ BddAbove (Set.range fun n : ℕ => (f (2 * n) : ℝ) / f n)`.

The definition `f` and the statement of `erdos_893.variants.unbounded` (category "research
solved") are copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/893.lean`, Apache-2.0), with the same namespace and name. There
`τ` is `σ 0`. The range includes `n = 0`, where `f 0 = 0` and the ratio is `0 / 0 = 0` in `ℝ`;
this single value does not affect unboundedness.

## Proof

* **Primitive prime divisors for `d ∣ 14^a`** (`exists_prime_orderOf_two_eq`). Let `1 < d` and
  `d ∣ 14^a`. By Mathlib, `|Φ_d(2)| > 1`, so some prime `p` divides `Φ_d(2)`. Then `2` is a root
  of `Φ_d` modulo `p`, and since `Φ_d ∣ X^d - 1` we get `2^d ≡ 1 (mod p)`. Hence `p ≠ 2`, and
  `p ≠ 7` because the order of `2` modulo `7` is `3`, which does not divide `d`. So `p ∤ 14`,
  hence `p ∤ d`, and `2` is a primitive `d`-th root of unity in `ZMod p`: the order of `2`
  modulo `p` is exactly `d`. (For this family of `d` the exceptions of the Bang–Zsigmondy theorem
  cannot occur, so that theorem is not needed.)
* **Many divisors** (`two_pow_le_sigma_zero`). Let `k = 14^a`. The primes `p_d` chosen above for
  the divisors `d > 1` of `k` all divide `2^k - 1` and are pairwise distinct, since the order of
  `2` modulo `p_d` recovers `d`. So `2^k - 1` has at least `τ(k) - 1 = (a + 1)^2 - 1` prime
  factors, and `τ(2^k - 1) ≥ 2^((a + 1)^2 - 1)`.
* **Conclusion** (`erdos_893.variants.unbounded`). Suppose `f(2n)/f(n) ≤ C` for all `n`. Since
  `f(n) > 0` for `n ≥ 1` and `f(1) = 1`, induction gives `f(2^m) ≤ C^m`. As
  `1 ≤ 14^b ≤ 2^(4b)`, we get `2^((b + 1)^2 - 1) ≤ τ(2^(14^b) - 1) ≤ f(2^(4b)) ≤ (C^4)^b`. Choosing
  `b ≥ 1` with `C^4 < 2^b` gives `(C^4)^b < 2^(b^2) ≤ 2^((b + 1)^2 - 1)`, a contradiction.

Kovač and Luca use Bang's theorem to get `τ(2^k - 1) ≥ 2^(τ(k) - 2)` for all `k`, prove with
highly composite numbers that `f'(2n)/f'(n) → ∞` for `f'(n) = ∑_{k ≤ n} 2^τ(k)`, and then use the
same final step `f(2^m) ≤ C^m`. The argument here keeps that final step but replaces Bang's
theorem and the highly composite numbers by the family `k = 14^a`, which is enough for
unboundedness.

## What remains open

Erdős Problem 893 itself (whether `f(2n)/f(n) → ∞`, the statement `erdos_893` in
formal-conjectures) is open and is not proved here. The conditional results of [KoLu25] (Theorem
3, under their Conjectures 1 or 2) and their Proposition 2 about `f'` are not formalized.

## References

* [Er98] Erdős, P., _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996), de Gruyter (1998), 169-180.
* [KoLu25] Kovač, V. and Luca, F., _On the number of divisors of Mersenne numbers_.
  arXiv:2506.04883 (2025).
* [erdosproblems.com/893](https://www.erdosproblems.com/893)
-/

open Filter Finset
open scoped ArithmeticFunction.sigma

namespace Erdos893

-- Copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/893.lean`.
/--
Definition of function $f(n) := \sum_{1\leq k\leq n}\tau(2^k-1)$.
Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
-/
def f (n : ℕ) : ℕ :=  ∑ k ∈ Finset.Icc 1 n, σ 0 (2^k - 1)

/-- The multiplicative order of `2` modulo `7` is `3`. -/
theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- If `1 < d` and `d ∣ 14 ^ a`, then some prime `p` has `2` of multiplicative order exactly `d`
modulo `p` (a prime factor of `Φ_d(2)`). -/
theorem exists_prime_orderOf_two_eq {a d : ℕ} (hd : 1 < d) (hda : d ∣ 14 ^ a) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = d := by
  have hv1 : 1 < ((Polynomial.cyclotomic d ℤ).eval ((2 : ℕ) : ℤ)).natAbs :=
    Polynomial.sub_one_lt_natAbs_cyclotomic_eval (q := 2) hd (by norm_num)
  obtain ⟨p, hp, hpv⟩ := Nat.exists_prime_and_dvd hv1.ne'
  have := Fact.mk hp
  have hpv' : (p : ℤ) ∣ (Polynomial.cyclotomic d ℤ).eval 2 := by
    simpa using Int.natCast_dvd.mpr hpv
  have hroot : (Polynomial.cyclotomic d (ZMod p)).IsRoot 2 := by
    have h := Polynomial.cyclotomic.eval_apply (2 : ℤ) d (Int.castRingHom (ZMod p))
    rw [Polynomial.IsRoot, show (2 : ZMod p) = Int.castRingHom (ZMod p) 2 by simp, h]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpv'
  have hpow : (2 : ZMod p) ^ d = 1 := by
    obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one d (ZMod p)
    have h := congrArg (Polynomial.eval (2 : ZMod p)) hg
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_mul, hroot.eq_zero, zero_mul] at h
    exact sub_eq_zero.mp h
  have hpd : ¬ p ∣ d := by
    intro hpd
    have hp14 : p ∣ 14 := hp.dvd_of_dvd_pow (hpd.trans hda)
    have hple : p ≤ 14 := Nat.le_of_dvd (by norm_num) hp14
    have h27 : p = 2 ∨ p = 7 := by
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)
    rcases h27 with rfl | rfl
    · rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    · have h3d : 3 ∣ d := orderOf_two_zmod_seven ▸ orderOf_dvd_iff_pow_eq_one.mpr hpow
      have : 3 ∣ 14 := (Nat.prime_three).dvd_of_dvd_pow (h3d.trans hda)
      omega
  have : NeZero (d : ZMod p) := ⟨fun h => hpd ((ZMod.natCast_eq_zero_iff d p).mp h)⟩
  exact ⟨p, hp, ((Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf).symm⟩

/-- `τ(2^(14^a) - 1) ≥ 2^((a + 1)^2 - 1)`: the divisors `d > 1` of `14^a` give pairwise distinct
prime factors of `2^(14^a) - 1`. -/
theorem two_pow_le_sigma_zero (a : ℕ) :
    2 ^ ((a + 1) * (a + 1) - 1) ≤ σ 0 (2 ^ (14 ^ a) - 1) := by
  set k := 14 ^ a with hk
  set N := 2 ^ k - 1 with hN
  have hk1 : 1 ≤ k := Nat.one_le_pow _ _ (by norm_num)
  have hN0 : N ≠ 0 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have hex : ∀ d ∈ k.divisors.erase 1, ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = d := by
    intro d hd
    obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
    have hdk : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hdk
      omega
    exact exists_prime_orderOf_two_eq (by omega) hdk
  choose! g hgp hgo using hex
  have hsub : (k.divisors.erase 1).image g ⊆ N.primeFactors := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    have hdk : d ∣ k := Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)
    have := Fact.mk (hgp d hd)
    have h1 : (2 : ZMod (g d)) ^ k = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hgo d hd]; exact hdk)
    have h2 : ((N : ℕ) : ZMod (g d)) = 0 := by
      rw [hN, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, h1, Nat.cast_one,
        sub_self]
    exact Nat.mem_primeFactors.mpr ⟨hgp d hd, (ZMod.natCast_eq_zero_iff N (g d)).mp h2, hN0⟩
  have hinj : Set.InjOn g (k.divisors.erase 1 : Set ℕ) := by
    intro d₁ h₁ d₂ h₂ heq
    rw [← hgo d₁ h₁, ← hgo d₂ h₂, heq]
  have hcardk : #k.divisors = (a + 1) * (a + 1) := by
    rw [hk, show (14 : ℕ) ^ a = 2 ^ a * 7 ^ a by rw [← mul_pow]; norm_num,
      Nat.Coprime.card_divisors_mul (Nat.Coprime.pow _ _ (by norm_num)),
      Nat.divisors_prime_pow Nat.prime_two, Nat.divisors_prime_pow (by norm_num)]
    simp
  have hcard : (a + 1) * (a + 1) - 1 ≤ #N.primeFactors := by
    calc (a + 1) * (a + 1) - 1 = #(k.divisors.erase 1) := by
          rw [Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr (by omega)), hcardk]
      _ = #((k.divisors.erase 1).image g) := (Finset.card_image_of_injOn hinj).symm
      _ ≤ #N.primeFactors := Finset.card_le_card hsub
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hN0]
  calc 2 ^ ((a + 1) * (a + 1) - 1) ≤ 2 ^ #N.primeFactors :=
        Nat.pow_le_pow_right (by norm_num) hcard
    _ ≤ N.primeFactors.prod (N.factorization · + 1) := by
        apply Finset.pow_card_le_prod
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hN0
          (Nat.dvd_of_mem_primeFactors hp)
        omega

-- Statement copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/893.lean`.
/--
Kovač and Luca [KoLu25] (building on a heuristic independently found by
Cambie (personal communication)) have shown that there is no finite limit, in that
$\lim_{n\to\infty} \frac{f(2n)}{f(n)}$ is unbounded.
-/
theorem erdos_893.variants.unbounded :
   ¬ BddAbove (Set.range fun n : ℕ => (f (2 * n) : ℝ) / f n) := by
  rintro ⟨C, hC⟩
  have hC' : ∀ n, (f (2 * n) : ℝ) / f n ≤ C := fun n => hC ⟨n, rfl⟩
  have hfpos : ∀ n, 1 ≤ n → 0 < f n := by
    intro n hn
    unfold f
    apply Finset.sum_pos
    · intro j hj
      apply ArithmeticFunction.sigma_pos
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Finset.mem_Icc.mp hj).1
      omega
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  have hstep : ∀ n, 1 ≤ n → (f (2 * n) : ℝ) ≤ C * f n := by
    intro n hn
    have := hC' n
    rwa [div_le_iff₀ (by exact_mod_cast hfpos n hn)] at this
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC' 1)
  have hpow : ∀ m, (f (2 ^ m) : ℝ) ≤ C ^ m := by
    intro m
    induction m with
    | zero => simp [f]
    | succ m ih =>
      rw [pow_succ', pow_succ']
      calc (f (2 * 2 ^ m) : ℝ) ≤ C * f (2 ^ m) := hstep _ Nat.one_le_two_pow
        _ ≤ C * C ^ m := mul_le_mul_of_nonneg_left ih hC0
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (C ^ 4) (by norm_num : (1 : ℝ) < 2)
  set b := a + 1 with hb
  have hle : σ 0 (2 ^ (14 ^ b) - 1) ≤ f (2 ^ (4 * b)) := by
    unfold f
    apply Finset.single_le_sum (f := fun j => σ 0 (2 ^ j - 1)) (fun _ _ => Nat.zero_le _)
    refine Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ (by norm_num), ?_⟩
    calc 14 ^ b ≤ 16 ^ b := Nat.pow_le_pow_left (by norm_num) b
      _ = 2 ^ (4 * b) := by rw [pow_mul]; norm_num
  have h1 : (2 : ℝ) ^ ((b + 1) * (b + 1) - 1) ≤ (C ^ 4) ^ b := by
    rw [← pow_mul]
    calc (2 : ℝ) ^ ((b + 1) * (b + 1) - 1) ≤ (σ 0 (2 ^ (14 ^ b) - 1) : ℝ) := by
          exact_mod_cast two_pow_le_sigma_zero b
      _ ≤ f (2 ^ (4 * b)) := by exact_mod_cast hle
      _ ≤ C ^ (4 * b) := hpow _
  have h2 : ((2 : ℝ) ^ b) ^ b ≤ (2 : ℝ) ^ ((b + 1) * (b + 1) - 1) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    have : b * b + 1 ≤ (b + 1) * (b + 1) := by nlinarith
    omega
  have h3 : (C ^ 4) ^ b < ((2 : ℝ) ^ b) ^ b := by
    have hlt : C ^ 4 < (2 : ℝ) ^ b :=
      ha.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
    exact pow_lt_pow_left₀ hlt (by positivity) (by omega)
  exact absurd (h1.trans_lt (h3.trans_le h2)) (lt_irrefl _)

end Erdos893
