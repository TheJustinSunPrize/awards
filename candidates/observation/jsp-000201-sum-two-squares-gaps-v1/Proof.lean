/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
import Mathlib

open scoped Function

/-!
# JSP-000201 — Lean formalization observation (complete answer)

**Problem (TheJustinSunPrize/awards, JSP-000201).** *How large can gaps between
consecutive integers representable as sums of two squares be?*

**Scope of this file.** This file formalizes the *complete answer* to the
catalog question: the gaps are **unbounded**. For every `k : ℕ` there exists an
`x : ℕ` such that none of the `k` consecutive integers `x + 1, ..., x + k` is a
sum of two squares:

```text
theorem jsp000201 : ∀ k : ℕ, ∃ x : ℕ, ∀ i, 1 ≤ i → i ≤ k →
    ¬ ∃ a b : ℕ, a * a + b * b = x + i
```

**The mathematical argument** is the classical elementary construction
(Hardy–Wright style), which we split into four lemmas:

1. There are infinitely many primes `p ≡ 3 (mod 4)`
   (`exists_prime_mod_four_eq_three_notMem`): Euclid-style, with
   `M = ∏ x ∈ s, max 1 x`, every prime factor of `4 * M * M - 1` avoids `s`,
   and since `4 * M * M - 1 ≡ 3 (mod 4)` at least one prime factor of it is
   `≡ 3 (mod 4)` (via `exists_prime_mod_four_eq_three_dvd`, a counting argument
   on the prime factorization: a product of primes all `≡ 1 (mod 4)` is
   `≡ 1 (mod 4)`).
2. Hence there are `k` pairwise distinct (indeed strictly increasing) primes
   `p 1, ..., p k ≡ 3 (mod 4)` (`exists_incr_primes_mod_four_eq_three`).
3. By the Chinese remainder theorem (`Nat.chineseRemainderOfFinset`) there is
   `x` with `x ≡ p i - i (mod p i ^ 2)` for all `1 ≤ i ≤ k`, i.e.
   `x + i ≡ p i (mod p i ^ 2)`; since `p i` is prime, `p i` divides `x + i`
   exactly once: `padicValNat (p i) (x + i) = 1`.
4. By Fermat's two-squares theorem (`Nat.eq_sq_add_sq_iff`), if
   `x + i = a * a + b * b` then the `p i`-adic valuation of `x + i` must be
   even — contradiction with `= 1`.

The original catalog entry remains Open (status field untouched); this
observation records the formalized complete answer to the question as posed.
It is not a claim on any award.

## Provenance / toolchain

* Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2` (pinned in `lean-toolchain`).
* No `sorry`, `admit`, `native_decide`, or unproven assumptions are used.
  Allowed axioms: `propext`, `Classical.choice`, `Quot.sound` (checked by
  `#print axioms jsp000201` at the end of this file).
-/

namespace JSP000201

/-! ### Helper: products of primes `≡ 1 (mod 4)` -/

/-- The product of a list of naturals each congruent to `1` mod `4` is again
congruent to `1` mod `4`. -/
private theorem prod_mod_four_eq_one {l : List ℕ} (h : ∀ x ∈ l, x % 4 = 1) :
    l.prod % 4 = 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.prod_cons, Nat.mul_mod]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [h1, h2]

/-- Every `n` with `n ≡ 3 (mod 4)` has a prime factor `q` with `q ≡ 3 (mod 4)`:
indeed a product of primes all `≡ 1 (mod 4)` is `≡ 1 (mod 4)`. -/
theorem exists_prime_mod_four_eq_three_dvd {n : ℕ} (hn4 : n % 4 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ q % 4 = 3 := by
  have hn0 : n ≠ 0 := by omega
  by_contra hcon
  have hall : ∀ x ∈ n.primeFactorsList, x % 4 = 1 := by
    intro x hx
    have hp : Nat.Prime x := Nat.prime_of_mem_primeFactorsList hx
    have hd : x ∣ n := Nat.dvd_of_mem_primeFactorsList hx
    rcases hp.eq_two_or_odd with heq | hodd
    · subst heq
      have h := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
    · rcases Nat.odd_mod_four_iff.mp hodd with h1 | h1
      · exact h1
      · exact absurd (⟨x, hp, hd, h1⟩ : ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ q % 4 = 3) hcon
  have hprod : n.primeFactorsList.prod % 4 = 3 := by
    rw [Nat.prod_primeFactorsList hn0]
    exact hn4
  rw [prod_mod_four_eq_one hall] at hprod
  omega

/-! ### Step 1: infinitely many primes `≡ 3 (mod 4)` -/

/-- For every finite set `s` of naturals there is a prime `q ≡ 3 (mod 4)`
with `q ∉ s`. Euclid-style: with `M = ∏ x ∈ s, max 1 x` every prime factor of
`4 * M * M - 1` is coprime to `M` (hence outside `s`), and since
`4 * M * M - 1 ≡ 3 (mod 4)` one of its prime factors is `≡ 3 (mod 4)`. -/
theorem exists_prime_mod_four_eq_three_notMem (s : Finset ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ∉ s := by
  set M : ℕ := s.prod (fun x => max 1 x) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Finset.one_le_prod (fun i _ => le_max_left 1 i)
  have hM2 : 1 ≤ M * M := by nlinarith
  have hN4 : (4 * (M * M) - 1) % 4 = 3 := by
    have hdvd : 4 ∣ 4 * (M * M) := ⟨M * M, by ring⟩
    have h0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  obtain ⟨q, hqp, hqd, hq4⟩ := exists_prime_mod_four_eq_three_dvd hN4
  refine ⟨q, hqp, hq4, ?_⟩
  intro hqs
  refine hqp.ne_one ?_
  have hqM : q ∣ M := by
    have h := Finset.dvd_prod_of_mem (fun x => max 1 x) (s := s) hqs
    rwa [max_eq_right (by have := hqp.two_le; omega)] at h
  have hqlt : 1 < q := by have := hqp.two_le; omega
  -- `q ∣ M` gives `q ∣ 4 * (M * M)`
  have hMMz : 4 * (M * M) % q = 0 := by
    obtain ⟨k, hk⟩ := hqM
    exact Nat.mod_eq_zero_of_dvd ⟨4 * (k * (q * k)), by rw [hk]; ring⟩
  -- `q ∣ 4 * (M * M) - 1` and `q ∣ 4 * (M * M)` force `q ∣ 1`
  have hqdz : (4 * (M * M) - 1) % q = 0 := Nat.mod_eq_zero_of_dvd hqd
  have hadd : 4 * (M * M) - 1 + 1 = 4 * (M * M) := by omega
  have h1 : 4 * (M * M) % q = 1 := by
    have h9 : (4 * (M * M) - 1 + 1) % q = ((4 * (M * M) - 1) % q + 1 % q) % q :=
      Nat.add_mod _ _ _
    rw [hadd, hqdz, Nat.zero_add, Nat.mod_eq_of_lt hqlt, Nat.mod_eq_of_lt hqlt] at h9
    exact h9
  rw [hMMz] at h1
  omega

/-- There are arbitrarily large primes `p ≡ 3 (mod 4)`. -/
theorem exists_prime_mod_four_eq_three_gt (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ n < p := by
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_prime_mod_four_eq_three_notMem
    (Finset.filter (fun p => p % 4 = 3 ∧ p ≤ n) (Finset.range (n + 1)))
  refine ⟨q, hq1, hq2, ?_⟩
  by_contra hcon
  exact hq3
    (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hq2, Nat.le_of_not_lt hcon⟩)

/-! ### Step 2: `k` pairwise distinct primes `≡ 3 (mod 4)` -/

/-- For every `k` there is a function assigning to each `1 ≤ i ≤ k` a prime
`p i ≡ 3 (mod 4)` with `i + 2 ≤ p i`, strictly increasing in `i`; in particular
the primes `p 1, ..., p k` are pairwise distinct. -/
theorem exists_incr_primes_mod_four_eq_three (k : ℕ) :
    ∃ p : ℕ → ℕ, ∀ i, 1 ≤ i → i ≤ k →
      Nat.Prime (p i) ∧ p i % 4 = 3 ∧ i + 2 ≤ p i ∧
        ∀ j, 1 ≤ j → j < i → p j < p i := by
  induction k with
  | zero =>
    refine ⟨fun _ => 3, ?_⟩
    intro i h1 h2
    exact absurd h2 (by omega)
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hqP, hq4, hqgt⟩ :=
      exists_prime_mod_four_eq_three_gt (if 1 ≤ k then p k else 2)
    have hpkq : ∀ j, 1 ≤ j → j ≤ k → p j < q := by
      intro j hj1 hjk
      by_cases hk : 1 ≤ k
      · rw [ite_eq_left hk] at hqgt
        rcases lt_or_eq_of_le hjk with h | h
        · exact Nat.lt_trans ((hp k hk (Nat.le_refl k)).2.2.2 j hj1 h) hqgt
        · rw [h]
          exact hqgt
      · omega
    refine ⟨fun i => if i ≤ k then p i else q, ?_⟩
    intro i h1 h2
    show Nat.Prime (if i ≤ k then p i else q) ∧
      (if i ≤ k then p i else q) % 4 = 3 ∧
      i + 2 ≤ (if i ≤ k then p i else q) ∧
      ∀ j, 1 ≤ j → j < i → (if j ≤ k then p j else q) < (if i ≤ k then p i else q)
    rcases Nat.eq_or_lt_of_le h2 with hik | hik
    · -- `i = k + 1`
      have hne : ¬ i ≤ k := by omega
      have hqi : i + 2 ≤ q := by
        by_cases hk : 1 ≤ k
        · have hC : k + 2 ≤ p k := (hp k hk (Nat.le_refl k)).2.2.1
          rw [ite_eq_left hk] at hqgt
          rw [hik]
          omega
        · rw [ite_eq_right hk] at hqgt
          rw [hik]
          omega
      rw [ite_eq_right hne]
      refine ⟨hqP, hq4, hqi, ?_⟩
      intro j hj1 hj2
      by_cases hjk : j ≤ k
      · rw [ite_eq_left hjk]
        exact hpkq j hj1 hjk
      · rw [ite_eq_right hjk]
        omega
    · -- `i ≤ k`
      have hik2 : i ≤ k := by omega
      have hprop := hp i h1 hik2
      rw [ite_eq_left hik2]
      refine ⟨hprop.1, hprop.2.1, hprop.2.2.1, ?_⟩
      intro j hj1 hj2
      rw [ite_eq_left (by omega)]
      exact hprop.2.2.2 j hj1 hj2

/-! ### Steps 3 and 4: CRT construction and Fermat's two-squares theorem -/

/-- **Main construction.** For every `k` there is `x` such that none of the
`k` consecutive integers `x + 1, ..., x + k` is a sum of two squares. -/
theorem exists_gap (k : ℕ) :
    ∃ x : ℕ, ∀ i, 1 ≤ i → i ≤ k →
      ¬ ∃ a b : ℕ, a * a + b * b = x + i := by
  classical
  obtain ⟨p, hp⟩ := exists_incr_primes_mod_four_eq_three k
  set a : ℕ → ℕ := fun i => p i - i with ha
  set s : ℕ → ℕ := fun i => p i ^ 2 with hs
  have hpk : ∀ i, 1 ≤ i → i ≤ k → Nat.Prime (p i) := fun i h1 h2 => (hp i h1 h2).1
  have hs0 : ∀ i ∈ Finset.Icc 1 k, s i ≠ 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    exact pow_ne_zero 2 (Nat.Prime.ne_zero (hpk i h1 h2))
  have hpair : Set.Pairwise (Finset.Icc 1 k : Set ℕ) (Nat.Coprime on s) := by
    intro i hi j hj hij
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    simp only [hs]
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hpine : p i ≠ p j := by
        intro hEq
        have hlt' : p i < p j := (hp j hj1 hj2).2.2.2 i hi1 hlt
        rw [hEq] at hlt'
        exact lt_irrefl _ hlt'
      exact Nat.coprime_pow_primes 2 2 (hpk i hi1 hi2) (hpk j hj1 hj2) hpine
    · exact absurd heq hij
    · have hpine : p j ≠ p i := by
        intro hEq
        have hgt' : p j < p i := (hp i hi1 hi2).2.2.2 j hj1 hgt
        rw [hEq] at hgt'
        exact lt_irrefl _ hgt'
      exact (Nat.coprime_pow_primes 2 2 (hpk j hj1 hj2) (hpk i hi1 hi2) hpine).symm
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset a s (Finset.Icc 1 k) hs0 hpair
  refine ⟨x, ?_⟩
  intro i h1 h2 hsum
  obtain ⟨a', b', hab⟩ := hsum
  obtain ⟨hprime, hmod4, hge, hmono⟩ := hp i h1 h2
  -- `x + i ≡ p i (mod p i ^ 2)`
  have hxm : x ≡ a i [MOD s i] := hx i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hxm2 : x + i ≡ p i [MOD p i ^ 2] := by
    have h5 := hxm.add_left i
    rw [Nat.add_comm i x,
      show i + (p i - i) = p i from Nat.add_sub_cancel' (by omega)] at h5
    exact h5
  have hmodEq : (x + i) % p i ^ 2 = p i % p i ^ 2 := hxm2
  have hplt : p i < p i ^ 2 := by
    have h2le : 2 ≤ p i := hprime.two_le
    rw [pow_two]
    nlinarith
  have hmod : (x + i) % p i ^ 2 = p i := by
    rw [hmodEq, Nat.mod_eq_of_lt hplt]
  -- `x + i = p i * (p i * c + 1)` for some `c`, so `p i` divides `x + i` exactly once
  obtain ⟨c, hc⟩ : ∃ c : ℕ, x + i = p i * (p i * c + 1) := by
    refine ⟨(x + i) / p i ^ 2, ?_⟩
    have hdm := Nat.div_add_mod (x + i) (p i ^ 2)
    rw [hmod] at hdm
    calc x + i = p i ^ 2 * ((x + i) / p i ^ 2) + p i := hdm.symm
      _ = p i * p i * ((x + i) / p i ^ 2) + p i := by rw [pow_two]
      _ = p i * (p i * ((x + i) / p i ^ 2) + 1) := by ring
  have hx0 : x + i ≠ 0 := by omega
  have hpowdvd : p i ∣ p i ^ 2 := by
    rw [pow_two]
    exact Nat.dvd_mul_right (p i) (p i)
  have hnd : ¬ p i ∣ p i * c + 1 := by
    intro hdvd
    obtain ⟨r, hr⟩ := hdvd
    refine hprime.ne_one ?_
    have h5 : p i ∣ 1 := ⟨r - c, by
      rw [Nat.mul_sub_left_distrib, ← hr, Nat.add_sub_cancel_left]⟩
    have h6 : p i ≤ 1 := Nat.le_of_dvd (by omega) h5
    omega
  have : Fact (p i).Prime := ⟨hprime⟩
  have hval : padicValNat (p i) (x + i) = 1 := by
    have hc0 : p i * c + 1 ≠ 0 := by omega
    rw [hc, padicValNat.mul (a := p i) (b := p i * c + 1) hprime.ne_zero hc0,
      padicValNat.self, padicValNat.eq_zero_of_not_dvd hnd]
    omega
  have hdvdpi : p i ∣ x + i := by
    apply Nat.dvd_of_mod_eq_zero
    have h1' := Nat.mod_mod_of_dvd (x + i) hpowdvd
    rw [hmodEq, Nat.mod_mod_of_dvd (p i) hpowdvd, Nat.mod_self] at h1'
    exact h1'.symm
  have hpf : p i ∈ (x + i).primeFactors :=
    hprime.mem_primeFactors hdvdpi hx0
  -- Fermat's two-squares theorem gives the contradiction
  have hab2 : x + i = a' ^ 2 + b' ^ 2 := by
    rw [pow_two, pow_two]
    exact hab.symm
  have hev : Even (padicValNat (p i) (x + i)) :=
    Nat.eq_sq_add_sq_iff.mp ⟨a', b', hab2⟩ (p i) hpf hmod4
  rw [hval] at hev
  exact Nat.not_even_one hev

end JSP000201

/-- **JSP-000201 (complete answer).** Gaps between consecutive sums of two
squares are unbounded: for every `k` there are `k` consecutive integers, none
of which is a sum of two squares. -/
theorem jsp000201 : ∀ k : ℕ, ∃ x : ℕ, ∀ i, 1 ≤ i → i ≤ k →
    ¬ ∃ a b : ℕ, a * a + b * b = x + i :=
  JSP000201.exists_gap

#print axioms jsp000201
