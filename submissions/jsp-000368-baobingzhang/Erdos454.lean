import Mathlib

/-!
# Erdős Problem 454, the bound `limsup (f n - 2 pₙ) ≥ 2` (Pomerance 1979)

Let `pₙ` be the `n`-th prime and `f n = min_{0 < i < n} (p_{n+i} + p_{n-i})`. Erdős asked whether
`limsup (f n - 2 pₙ) = ∞`. Pomerance [Po79] proved `limsup (f n - 2 pₙ) ≥ 2`: for infinitely many
`n`, `p_{n+i} + p_{n-i} ≥ 2 pₙ + 2` for every `0 < i < n`.

The definition `f` and the statement `erdos_454.variants.two_le_limsup` are copied verbatim from
Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/454.lean`,
Apache-2.0). As there, primes are indexed from `0` via `Nat.nth Prime` (so `Nat.nth Prime 0 = 2`),
`Prime` is `_root_.Prime` on `ℕ` (equivalent to `Nat.Prime`), and `f n = 0` for `n ≤ 1`.

Proof (Pomerance's convex-hull argument, made elementary):
* `primorial x ≤ 4 ^ x` gives `c * m ≤ c * 4 ^ c + pₘ` for all `c, m`, so `pₘ - s m → ∞` for each `s`;
* the largest minimiser `n` of `m ↦ pₘ - s m` satisfies `p_{n-i} + p_{n+i} > 2 pₙ`, and taking
  `s > p_{N+1}` forces `n > N`;
* `p_{n±i}` are odd (their indices are `≥ 1`), which upgrades `> 2 pₙ` to `≥ 2 pₙ + 2`.

*References:*
 - [erdosproblems.com/454](https://www.erdosproblems.com/454)
 - [Po79] Pomerance, Carl, The prime number graph. Math. Comp. (1979), 399-408.
-/

open Filter

namespace Erdos454

/-- Define `f n` to be the minimum of `(n + i).nth Prime + (n - i).nth Prime` over `0 < i < n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⨅ i : {i : Fin n // 0 < (i : ℕ)}, (n + i).nth Prime + (n - i).nth Prime

/-- On `ℕ`, `_root_.Prime` and `Nat.Prime` agree, so the formal-conjectures indexing
`Nat.nth Prime` is Mathlib's `Nat.nth Nat.Prime`. -/
theorem nth_Prime_eq : Nat.nth (Prime : ℕ → Prop) = Nat.nth Nat.Prime := by
  congr 1; funext p; exact propext Nat.prime_iff.symm

/-- An elementary Chebyshev-type bound, from `primorial x ≤ 4 ^ x`: if `k` primes below `x` are
`≥ 4 ^ c`, then `(4 ^ c) ^ k ≤ 4 ^ x`, so `c * k ≤ x`; the remaining primes below `x` are fewer
than `4 ^ c`. Hence `π'(x) ≤ 4 ^ c + x / c`. -/
theorem mul_primeCounting'_le (c x : ℕ) :
    c * Nat.primeCounting' x ≤ c * 4 ^ c + x := by
  classical
  have hT : Nat.primeCounting' x = ((Finset.range x).filter Nat.Prime).card :=
    Nat.count_eq_card_filter_range _ _
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range x).filter Nat.Prime) (fun p => 4 ^ c ≤ p)
  have hsmall : (((Finset.range x).filter Nat.Prime).filter (fun p => ¬ 4 ^ c ≤ p)).card
      ≤ 4 ^ c := by
    calc _ ≤ (Finset.range (4 ^ c)).card := Finset.card_le_card (by
            intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
            omega)
      _ = 4 ^ c := Finset.card_range _
  have hprod : (4 ^ c) ^ (((Finset.range x).filter Nat.Prime).filter (fun p => 4 ^ c ≤ p)).card
      ≤ 4 ^ x := by
    calc _ ≤ ∏ p ∈ ((Finset.range x).filter Nat.Prime).filter (fun p => 4 ^ c ≤ p), p :=
          Finset.pow_card_le_prod _ _ _ (by
            intro p hp
            exact (Finset.mem_filter.mp hp).2)
      _ ≤ ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p :=
          Finset.prod_le_prod_of_subset_of_one_le (by
            intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
            exact ⟨by omega, hp.1.2⟩)
            (by
              intro p hp _
              exact (Finset.mem_filter.mp hp).2.one_lt.le)
      _ = primorial x := rfl
      _ ≤ 4 ^ x := primorial_le_four_pow x
  have hcS : c * (((Finset.range x).filter Nat.Prime).filter (fun p => 4 ^ c ≤ p)).card ≤ x := by
    rw [← pow_mul] at hprod
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hprod
  rw [hT, ← hsplit, mul_add]
  have := Nat.mul_le_mul_left c hsmall
  omega

/-- Superlinear growth of the primes: `c * m ≤ c * 4 ^ c + p_m` for every `c`, where
`p_m = Nat.nth Nat.Prime m` (so `p_0 = 2`). -/
theorem mul_le_nth_prime (c m : ℕ) : c * m ≤ c * 4 ^ c + Nat.nth Nat.Prime m := by
  simpa [Nat.primeCounting'_nth_eq] using mul_primeCounting'_le c (Nat.nth Nat.Prime m)

/-- A function `g : ℕ → ℤ` with `g m ≥ m - K` has a *largest* global minimiser `n`: `g n ≤ g j`
for all `j`, and `g n < g j` for all `j > n`. -/
theorem exists_last_min (g : ℕ → ℤ) (K : ℕ) (hg : ∀ m : ℕ, (m : ℤ) - K ≤ g m) :
    ∃ n, (∀ j, g n ≤ g j) ∧ ∀ j, n < j → g n < g j := by
  classical
  set b := K + (g 0).toNat
  have hbig : ∀ j, b < j → g 0 < g j := by
    intro j hj
    have := hg j
    have h0 := Int.self_le_toNat (g 0)
    omega
  obtain ⟨m0, hm0, hmin⟩ := (Finset.range (b + 1)).exists_min_image g ⟨0, by simp⟩
  have hP : ∀ j, g m0 ≤ g j := by
    intro j
    by_cases hj : j ≤ b
    · exact hmin j (by simp; omega)
    · exact (hmin 0 (by simp)).trans (hbig j (by omega)).le
  have hm0b : m0 ≤ b := by simp at hm0; omega
  set n := Nat.findGreatest (fun m => ∀ j, g m ≤ g j) b
  have hn : ∀ j, g n ≤ g j := Nat.findGreatest_spec (P := fun m => ∀ j, g m ≤ g j) hm0b hP
  refine ⟨n, hn, fun j hj => ?_⟩
  by_contra hle
  replace hle := not_lt.mp hle
  by_cases hjb : j ≤ b
  · have : j ≤ n := Nat.le_findGreatest (P := fun m => ∀ j, g m ≤ g j) hjb
      (fun k => hle.trans (hn k))
    omega
  · have h1 := hbig j (by omega)
    have h2 := hn 0
    omega

/-- Pomerance's argument (with `Nat.Prime`). Put `s = p_{N+1} + 1` and `g m = p_m - s * m`, which
tends to `+∞` by `mul_le_nth_prime`. Let `n` be the largest minimiser of `g`; `s > p_{N+1}` forces
`n > N`. For `0 < i < n`, `g (n - i) ≥ g n` and `g (n + i) > g n` give
`p_{n+i} + p_{n-i} > 2 p_n`, and since `n ± i ≥ 1` both primes are odd, so the sum is even and
`p_{n+i} + p_{n-i} ≥ 2 p_n + 2`. -/
theorem exists_gt_forall_two_mul_add_two_le (N : ℕ) :
    ∃ n > N, ∀ i, 0 < i → i < n →
      2 * Nat.nth Nat.Prime n + 2 ≤ Nat.nth Nat.Prime (n + i) + Nat.nth Nat.Prime (n - i) := by
  set p := Nat.nth Nat.Prime with hp
  set s := p (N + 1) + 1 with hs
  let g : ℕ → ℤ := fun m => (p m : ℤ) - s * m
  have hg : ∀ m : ℕ, (m : ℤ) - ((s + 1) * 4 ^ (s + 1) : ℕ) ≤ g m := by
    intro m
    have h := mul_le_nth_prime (s + 1) m
    have h' : ((s + 1 : ℕ) : ℤ) * m ≤ ((s + 1 : ℕ) : ℤ) * 4 ^ (s + 1) + p m := by
      exact_mod_cast h
    simp only [g]
    push_cast at h' ⊢
    nlinarith
  obtain ⟨n, hmin, hlast⟩ := exists_last_min g _ hg
  have hnN : N < n := by
    by_contra h
    replace h := not_lt.mp h
    have h1 := hmin (N + 1)
    simp only [g] at h1
    have hpn : (0 : ℤ) ≤ p n := by positivity
    have hn1 : (n : ℤ) + 1 ≤ N + 1 := by exact_mod_cast Nat.succ_le_succ h
    have hs0 : (0 : ℤ) ≤ s := by positivity
    have hsn : (s : ℤ) * n + s ≤ s * (N + 1) := by nlinarith
    push_cast [hs] at h1 hsn
    linarith
  refine ⟨n, hnN, fun i hi hin => ?_⟩
  have h1 := hmin (n - i)
  have h2 := hlast (n + i) (by omega)
  simp only [g] at h1 h2
  rw [Nat.cast_sub hin.le] at h1
  push_cast at h2
  have hsum : 2 * (p n : ℤ) < p (n + i) + p (n - i) := by linarith
  have hodd : ∀ k, 0 < k → p k % 2 = 1 := by
    intro k hk
    apply Nat.odd_iff.mp
    apply (Nat.prime_nth_prime k).odd_of_ne_two
    have := Nat.add_two_le_nth_prime k
    omega
  have := hodd (n + i) (by omega)
  have := hodd (n - i) (by omega)
  omega

/-- Pomerance's theorem in the formal-conjectures indexing: for every `N` there is `n > N` with
`p_{n+i} + p_{n-i} ≥ 2 pₙ + 2` for all `0 < i < n`. -/
theorem exists_gt_forall_nth_prime_add_nth_prime (N : ℕ) :
    ∃ n > N, ∀ i, 0 < i → i < n →
      2 * n.nth Prime + 2 ≤ (n + i).nth Prime + (n - i).nth Prime := by
  rw [nth_Prime_eq]
  exact exists_gt_forall_two_mul_add_two_le N

/-- If `n ≥ 2` and every `p_{n+i} + p_{n-i}` (`0 < i < n`) is at least `2 pₙ + 2`, then so is
their minimum `f n`. -/
theorem two_mul_add_two_le_f {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ i, 0 < i → i < n → 2 * n.nth Prime + 2 ≤ (n + i).nth Prime + (n - i).nth Prime) :
    2 * n.nth Prime + 2 ≤ f n := by
  have hn1 : ¬ n ≤ 1 := by omega
  simp only [f, hn1, ↓reduceIte]
  have : Nonempty {i : Fin n // 0 < (i : ℕ)} := ⟨⟨⟨1, by omega⟩, Nat.one_pos⟩⟩
  exact le_ciInf fun i => h i i.2 i.1.2

/-- `f n ≥ 2 pₙ + 2` for infinitely many `n` (such `n` automatically have `n ≥ 2`, since
`f n = 0` for `n ≤ 1`). -/
theorem frequently_two_mul_nth_prime_add_two_le_f :
    ∃ᶠ n in atTop, 2 * n.nth Prime + 2 ≤ f n := by
  refine frequently_atTop.mpr fun N => ?_
  obtain ⟨n, hn, h⟩ := exists_gt_forall_nth_prime_add_nth_prime (N + 1)
  exact ⟨n, by omega, two_mul_add_two_le_f (by omega) h⟩

/-- **Pomerance (1979).** `limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop ≥ 2`.
This is the statement `erdos_454.variants.two_le_limsup` of formal-conjectures, now proved. -/
theorem erdos_454.variants.two_le_limsup :
    2 ≤ limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop := by
  refine le_limsup_of_frequently_le (frequently_two_mul_nth_prime_add_two_le_f.mono fun n hn => ?_)
  have : 2 ≤ f n - 2 * n.nth Prime := by omega
  exact_mod_cast this

end Erdos454
