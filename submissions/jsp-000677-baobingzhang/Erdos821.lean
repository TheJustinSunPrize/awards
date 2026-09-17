import Mathlib

/-!
# Erdős Problem 821: Pillai's theorem `limsup g(n) = ∞`

Let `g(n)` count the `m` with `φ(m) = n`. Erdős asked (open) whether `g(n) > n^(1-ε)` for
infinitely many `n`. Pillai (1929) proved that `g` is unbounded, i.e. `limsup g(n) = ∞`; this file
proves that result, stated without proof as `erdos_821.variants.pillai` (category
"research solved") in Google DeepMind's formal-conjectures project,
`FormalConjectures/ErdosProblems/821.lean`. The definition of `g` and the statement of
`erdos_821.variants.pillai` are copied verbatim from that project (Apache-2.0).

## Proof

* `g n` is the `ncard` of `{m | φ m = n}`, and this set is finite (`finite_setOf_totient_eq`):
  it is `{0}` for `n = 0`, and for `n ≥ 1` every prime `p ∣ m` has `p - 1 = φ p ∣ φ m = n`, so
  `p ≤ n + 1`, and Euler's product formula `m ∏ (p - 1) = φ(m) ∏ p` gives
  `m ≤ n (n + 1) ^ (n + 2)`.
* Let `R` be a finite set of primes with `q ∤ q' - 1` for all `q, q' ∈ R`, and
  `A = ∏_{q ∈ R} (q - 1)`. No `q ∈ R` divides `A`, while every prime factor of every `q - 1`
  divides `A`. For `U ⊆ R` put `m_U = A · ∏_{q ∈ R \ U} (q - 1) · ∏_{q ∈ U} q`. Then the prime
  factors of `m_U` are `primeFactors A ⊔ U` (disjoint), so Euler's product formula gives
  `φ(m_U) · P · ∏_U q = A² · Q · ∏_U q` with `P = ∏_{p ∣ A} p`, `Q = ∏_{p ∣ A} (p - 1)`,
  hence `φ(m_U) = φ(A²)` for every `U`. As `U` is recovered from the prime factors of `m_U`,
  `g(φ(A²)) ≥ 2 ^ |R|` (`two_pow_card_le_g`).
* Sets `R` of every size exist (`exists_finset_primes`): given `R` of odd primes, Dirichlet's
  theorem gives a prime `p > ∏ R + 2` with `p ≡ -1 (mod ∏ R)`. Then `q ∣ p - 1` for `q ∈ R`
  would give `q ∣ 2`, and `p ∤ q - 1` since `0 < q - 1 < p`.
* Hence `g` is unbounded; since `g` is bounded on `[0, N)`, `K ≤ g n` holds frequently, and so
  every real number lies below the `EReal` limsup.
-/

open Nat Filter

namespace Erdos821

/--
Let $g(n)$ count the number of $m$ such that $\phi(m)=n$.
-/
noncomputable def g (n : ℕ) : ℕ :=
  { m : ℕ | totient m = n }.ncard

/-- The set of solutions of `φ m = n` is finite, so `g n` really counts them. -/
theorem finite_setOf_totient_eq (n : ℕ) : {m : ℕ | totient m = n}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (Set.finite_singleton 0).subset fun m hm => ?_
    simpa using hm
  · refine (Set.finite_Iic (n * (n + 1) ^ (n + 2))).subset fun m hm => ?_
    simp only [Set.mem_ofPred_eq] at hm
    have hsub : m.primeFactors ⊆ Finset.range (n + 2) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd := Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
      rw [Nat.totient_prime hpp, hm] at hdvd
      have := Nat.le_of_dvd hn hdvd
      simp only [Finset.mem_range]
      omega
    have key := Nat.totient_mul_prod_primeFactors m
    rw [hm] at key
    have h1 : 1 ≤ ∏ p ∈ m.primeFactors, (p - 1) := by
      apply Finset.one_le_prod
      intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    have h2 : ∏ p ∈ m.primeFactors, p ≤ (n + 1) ^ (n + 2) := by
      calc ∏ p ∈ m.primeFactors, p ≤ (n + 1) ^ m.primeFactors.card :=
            Finset.prod_le_pow_card _ _ _ fun p hp => by
              have := hsub hp
              simp only [Finset.mem_range] at this
              omega
        _ ≤ (n + 1) ^ (n + 2) :=
            Nat.pow_le_pow_right (by omega) (by simpa using Finset.card_le_card hsub)
    show m ≤ n * (n + 1) ^ (n + 2)
    calc m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.le_mul_of_pos_right _ h1
      _ = n * ∏ p ∈ m.primeFactors, p := key.symm
      _ ≤ n * (n + 1) ^ (n + 2) := Nat.mul_le_mul_left _ h2

/-- If `R` is a finite set of primes such that no `q ∈ R` divides `q' - 1` for `q' ∈ R`, then
with `A = ∏_{q ∈ R} (q - 1)` the value `φ(A²)` has at least `2 ^ |R|` preimages under `φ`,
namely `A · ∏_{q ∈ R \ U} (q - 1) · ∏_{q ∈ U} q` for `U ⊆ R`. -/
theorem two_pow_card_le_g {R : Finset ℕ} (hR : ∀ q ∈ R, q.Prime)
    (hdiv : ∀ q ∈ R, ∀ q' ∈ R, ¬ q ∣ q' - 1) :
    2 ^ R.card ≤ g (totient ((∏ q ∈ R, (q - 1)) * ∏ q ∈ R, (q - 1))) := by
  set A := ∏ q ∈ R, (q - 1) with hA
  set m : Finset ℕ → ℕ := fun U => A * (∏ q ∈ R \ U, (q - 1)) * ∏ q ∈ U, q with hm
  have hsub1 : ∀ q ∈ R, q - 1 ≠ 0 := fun q hq => by
    have := (hR q hq).two_le
    omega
  have hA0 : A ≠ 0 := Finset.prod_ne_zero_iff.mpr hsub1
  have hS : ∀ U ⊆ R, (m U).primeFactors = A.primeFactors ∪ U := by
    intro U hU
    have h1 : (∏ q ∈ R \ U, (q - 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => hsub1 q (Finset.sdiff_subset hq)
    have h2 : (∏ q ∈ U, q) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => (hR q (hU hq)).ne_zero
    have h3 : (∏ q ∈ R \ U, (q - 1)).primeFactors ⊆ A.primeFactors :=
      Nat.primeFactors_mono (Finset.prod_dvd_prod_of_subset _ _ _ Finset.sdiff_subset) hA0
    simp only [hm]
    rw [Nat.primeFactors_mul (mul_ne_zero hA0 h1) h2, Nat.primeFactors_mul hA0 h1,
      Nat.primeFactors_prod fun q hq => hR q (hU hq), Finset.union_eq_left.mpr h3]
  have hdisj : ∀ U ⊆ R, Disjoint A.primeFactors U := by
    intro U hU
    rw [Finset.disjoint_right]
    intro q hq hqA
    have hqA' : q ∣ ∏ q ∈ R, (q - 1) := Nat.dvd_of_mem_primeFactors hqA
    obtain ⟨q', hq', hdvd⟩ := ((hR q (hU hq)).prime.dvd_finsetProd_iff _).mp hqA'
    exact hdiv q (hU hq) q' hq' hdvd
  have hphi : ∀ U ⊆ R, totient (m U) = totient (A * A) := by
    intro U hU
    have e1 := Nat.totient_mul_prod_primeFactors (m U)
    have e2 := Nat.totient_mul_prod_primeFactors (A * A)
    rw [hS U hU, Finset.prod_union (hdisj U hU), Finset.prod_union (hdisj U hU)] at e1
    rw [Nat.primeFactors_mul hA0 hA0, Finset.union_self] at e2
    have hsplit : (∏ q ∈ R \ U, (q - 1)) * ∏ q ∈ U, (q - 1) = A := Finset.prod_sdiff hU
    have hP : 0 < ∏ p ∈ A.primeFactors, p :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hU0 : 0 < ∏ q ∈ U, q := Finset.prod_pos fun q hq => (hR q (hU hq)).pos
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hP hU0)
    calc totient (m U) * ((∏ p ∈ A.primeFactors, p) * ∏ q ∈ U, q)
        = m U * ((∏ p ∈ A.primeFactors, (p - 1)) * ∏ q ∈ U, (q - 1)) := e1
      _ = (A * ((∏ q ∈ R \ U, (q - 1)) * ∏ q ∈ U, (q - 1)) * ∏ p ∈ A.primeFactors, (p - 1)) *
            ∏ q ∈ U, q := by
          simp only [hm]
          ring
      _ = (A * A * ∏ p ∈ A.primeFactors, (p - 1)) * ∏ q ∈ U, q := by rw [hsplit]
      _ = totient (A * A) * ((∏ p ∈ A.primeFactors, p) * ∏ q ∈ U, q) := by
          rw [← e2]
          ring
  have hinj : Set.InjOn m R.powerset := by
    intro U hU V hV hUV
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hU hV
    have h := congrArg Nat.primeFactors hUV
    rw [hS U hU, hS V hV] at h
    ext q
    constructor
    · intro hq
      have hq' : q ∈ A.primeFactors ∪ V := h ▸ Finset.mem_union_right _ hq
      rcases Finset.mem_union.mp hq' with h' | h'
      · exact absurd h' (Finset.disjoint_right.mp (hdisj U hU) hq)
      · exact h'
    · intro hq
      have hq' : q ∈ A.primeFactors ∪ U := h.symm ▸ Finset.mem_union_right _ hq
      rcases Finset.mem_union.mp hq' with h' | h'
      · exact absurd h' (Finset.disjoint_right.mp (hdisj V hV) hq)
      · exact h'
  have hsub : (↑(R.powerset.image m) : Set ℕ) ⊆ {x | totient x = totient (A * A)} := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_powerset] at hx
    obtain ⟨U, hU, rfl⟩ := hx
    exact hphi U hU
  calc 2 ^ R.card = (R.powerset.image m).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
    _ = (↑(R.powerset.image m) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ g (totient (A * A)) := Set.ncard_le_ncard hsub (finite_setOf_totient_eq _)

/-- For every `K` there is a set of `K` odd primes `R` with `q ∤ q' - 1` for all `q, q' ∈ R`
(built with Dirichlet's theorem: each new prime is `≡ -1` modulo the product of the old ones). -/
theorem exists_finset_primes (K : ℕ) :
    ∃ R : Finset ℕ, R.card = K ∧ (∀ q ∈ R, q.Prime ∧ 2 < q) ∧
      ∀ q ∈ R, ∀ q' ∈ R, ¬ q ∣ q' - 1 := by
  induction K with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨R, hcard, hpr, hdiv⟩ := ih
    set N := ∏ q ∈ R, q with hN
    have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hpr q hq).1.ne_zero
    have : NeZero N := ⟨hN0⟩
    obtain ⟨p, hpN, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := N) (a := -1) isUnit_one.neg (N + 2)
    have hNdvd : N ∣ p + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [hpmod]
      ring
    have hqle : ∀ q ∈ R, q ≤ N := fun q hq =>
      Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (Finset.dvd_prod_of_mem (fun x => x) hq)
    have hpR : p ∉ R := fun h => by
      have := hqle p h
      omega
    refine ⟨insert p R, by rw [Finset.card_insert_of_notMem hpR, hcard], ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact ⟨hp, by omega⟩
      · exact hpr q hq
    · intro q hq q' hq'
      rw [Finset.mem_insert] at hq hq'
      rcases hq with rfl | hq <;> rcases hq' with rfl | hq'
      · intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      · intro h
        have h2 := (hpr q' hq').2
        have := Nat.le_of_dvd (by omega) h
        have := hqle q' hq'
        omega
      · intro h
        have h1 : q ∣ q' + 1 := (Finset.dvd_prod_of_mem (fun x => x) hq).trans hNdvd
        have h2 : q ∣ (q' + 1) - (q' - 1) := Nat.dvd_sub h1 h
        have h3 : (q' + 1) - (q' - 1) = 2 := by omega
        rw [h3] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        have := (hpr q hq).2
        omega
      · exact hdiv q hq q' hq'

/-- `g` is unbounded. -/
theorem exists_le_g (K : ℕ) : ∃ n, K ≤ g n := by
  obtain ⟨R, hcard, hpr, hdiv⟩ := exists_finset_primes K
  refine ⟨totient ((∏ q ∈ R, (q - 1)) * ∏ q ∈ R, (q - 1)), ?_⟩
  calc K ≤ 2 ^ K := (Nat.lt_two_pow_self).le
    _ = 2 ^ R.card := by rw [hcard]
    _ ≤ _ := two_pow_card_le_g (fun q hq => (hpr q hq).1) hdiv

/-- For every `K`, `K ≤ g n` for arbitrarily large `n`. -/
theorem frequently_le_g (K : ℕ) : ∃ᶠ n in atTop, K ≤ g n := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, hn⟩ := exists_le_g (K + ∑ i ∈ Finset.range a, g i + 1)
  refine ⟨n, ?_, by omega⟩
  by_contra h
  have := Finset.single_le_sum (f := g) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.mpr (not_le.mp h))
  omega

/--
Pillai proved that $\limsup g(n)=\infty$.
-/
theorem erdos_821.variants.pillai :
    atTop.limsup (fun n : ℕ ↦ (g n : EReal)) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨K, hK⟩ := exists_nat_gt y
  have h : ∃ᶠ n in atTop, (K : EReal) ≤ (g n : EReal) :=
    (frequently_le_g K).mono fun n hn => by exact_mod_cast hn
  calc (y : EReal) < (K : EReal) := by exact_mod_cast hK
    _ ≤ atTop.limsup (fun n : ℕ ↦ (g n : EReal)) := le_limsup_of_frequently_le h

end Erdos821
