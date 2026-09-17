import Mathlib

set_option maxRecDepth 100000

open Nat Finset

/-!
# JSP-000595 · Factorial squares dividing double factorials

Erdős, Graham, Ruzsa and Straus (EGRS75, *On the prime factors of
`C(2n,n)`*) asked whether `(n + k)!² ∣ (2n)!` happens for infinitely many
`n`, for each fixed `k ≥ 2`; the case `k = 1` (equivalently
`(n + 1)² ∣ C(2n,n)`) was settled affirmatively by Balakran in 1929.
The problem is open for every `k ≥ 2`; in particular even the bare
existence of solutions is part of the conjectured picture.

This file formalizes the existential content of the catalogue entry
(JSP-000595): explicit certified witnesses for `k = 1, 2, 3`, a
monotonicity observation in `k`, an elementary *prime obstruction*
(a prime in `(n, n + k]` blocks the divisibility), and a kernel-checked
proof that `n = 208` is the least `k = 2` witness.

The stronger question — infinitude for any fixed `k ≥ 2` — is open and is
*not* claimed here.
-/

/-- `(n + k)!² ∣ (2n)!`: the square of a factorial with index slightly
above `n` divides the factorial of `2n`. -/
def FactSqDivides (n k : ℕ) : Prop :=
  (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)

/-- The Legendre sum `∑_{1 ≤ i < 20} n / p^i`; equals
`(n!).factorization p` whenever `p` is prime and `n < p ^ 20`. -/
def legSum (n p : ℕ) : ℕ := ∑ i ∈ Ico 1 20, n / p ^ i

theorem legSum_eq_factorization {n p : ℕ} (hp : p.Prime) (h : n < p ^ 20) :
    legSum n p = (Nat.factorial n).factorization p := by
  unfold legSum
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' (by norm_num) h)]

/-- If `(n + k)!² ∣ (2n)!` then `2 * v_p((n+k)!) ≤ v_p((2n)!)` for every
prime `p`. -/
theorem two_mul_legSum_le {n k p : ℕ} (hk : k ≤ n) (hn : 2 * n < p ^ 20)
    (hp : p.Prime) (h : FactSqDivides n k) :
    2 * legSum (n + k) p ≤ legSum (2 * n) p := by
  have hle := Finsupp.le_def.mp
    ((Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mpr h) p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hle
  rw [← legSum_eq_factorization hp (by omega : n + k < p ^ 20),
    ← legSum_eq_factorization hp hn] at hle
  exact hle

/-- **Prime obstruction.** A prime `p` with `n < p ≤ n + k` (and `k ≤ n`)
forces `(n + k)!² ∤ (2n)!`: `p` occurs once in `(n + k)!` but only once in
`(2n)!` as well, so the square cannot divide. -/
theorem not_factSqDivides_of_prime_between {n k p : ℕ} (hn : 2 ≤ n) (hk : k ≤ n)
    (hp : Nat.Prime p) (hlo : n < p) (hhi : p ≤ n + k) : ¬ FactSqDivides n k := by
  intro h
  have hgt : n + k < p ^ 2 := by nlinarith
  have hgt2 : 2 * n < p ^ 2 := by nlinarith
  have hlt2p : n + k < 2 * p := by omega
  have hdiv1 : (n + k) / p = 1 := Nat.div_eq_of_lt_le (by omega) hlt2p
  have hpk : (Nat.factorial (n + k)).factorization p = 1 := by
    rw [Nat.factorization_factorial hp
      (show Nat.log p (n + k) < 2 from
        (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).mpr hgt)]
    rw [show Ico 1 2 = {1} from rfl, Finset.sum_singleton, pow_one, hdiv1]
  have hp2n : (Nat.factorial (2 * n)).factorization p = 1 := by
    rw [Nat.factorization_factorial hp
      (show Nat.log p (2 * n) < 2 from
        (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).mpr hgt2)]
    rw [show Ico 1 2 = {1} from rfl, Finset.sum_singleton, pow_one]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hle := Finsupp.le_def.mp
    ((Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mpr h) p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpk, hp2n] at hle
  omega

/-- The divisibility is downward-closed in `k`: a witness at offset `l`
certifies every smaller offset. -/
theorem FactSqDivides.mono {n k l : ℕ} (hkl : k ≤ l) (h : FactSqDivides n l) :
    FactSqDivides n k :=
  (pow_dvd_pow_of_dvd
    (Nat.factorial_dvd_factorial (show n + k ≤ n + l by omega)) 2).trans h

/-- `k = 1`: the classical Balakran case; `n = 5` works since
`6!² = 518400` divides `10! = 3628800` (quotient `7`). -/
theorem factSqDivides_5_1 : FactSqDivides 5 1 := by
  unfold FactSqDivides; decide

/-- `k = 2`, least witness: `(210)!² ∣ (416)!`. -/
theorem factSqDivides_208_2 : FactSqDivides 208 2 := by
  unfold FactSqDivides; decide

/-- `k = 2`, further certified witnesses. -/
theorem factSqDivides_458_2 : FactSqDivides 458 2 := by
  unfold FactSqDivides; decide

theorem factSqDivides_987_2 : FactSqDivides 987 2 := by
  unfold FactSqDivides; decide

/-- `k = 3`, least witness: `(3478)!² ∣ (6950)!`. -/
theorem factSqDivides_3475_3 : FactSqDivides 3475 3 := by
  unfold FactSqDivides; decide

/-- `k = 4` witness `n = 8174` (also the second `k = 3` witness): the
offsets are nested since `(n + k)!² ∣ (n + k + 1)!²`. -/
theorem factSqDivides_8174_4 : FactSqDivides 8174 4 := by
  unfold FactSqDivides; decide

/-- **JSP-000595.** There exist `n` and `k ≥ 2` with `(n + k)!² ∣ (2n)!`;
witness `n = 208`, `k = 2`. -/
theorem jsp_000595 : ∃ n k : ℕ, 2 ≤ k ∧ FactSqDivides n k :=
  ⟨208, 2, le_refl 2, factSqDivides_208_2⟩

/-- Minimality of the `k = 2` witness: every `2 ≤ n ≤ 207` fails, since
some prime `p ≤ 2n` has `2 · v_p((n+2)!) > v_p((2n)!)`.  The check is a
pure small-number computation on truncated Legendre sums. -/
private theorem k2_obstruction_below_208 :
    ∀ n ∈ Finset.Icc 2 207,
      ∃ p ∈ (Finset.Icc 2 416).filter Nat.Prime,
        legSum (2 * n) p < 2 * legSum (n + 2) p := by
  decide

theorem jsp_000595_least_k2 {n : ℕ} (hn : 2 ≤ n) (h : FactSqDivides n 2) :
    208 ≤ n := by
  by_contra hlt
  have hlt' : n ≤ 207 := by omega
  obtain ⟨p, hp_mem, hpval⟩ :=
    k2_obstruction_below_208 n (Finset.mem_Icc.mpr ⟨hn, hlt'⟩)
  rw [Finset.mem_filter] at hp_mem
  have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp_mem.1).1
  have hbound : 2 * n < p ^ 20 := by
    calc 2 * n ≤ 2 * 207 := by omega
    _ < 2 ^ 20 := by norm_num
    _ ≤ p ^ 20 := Nat.pow_le_pow_left hp2 20
  exact absurd hpval
    (not_lt_of_ge (two_mul_legSum_le (by omega) hbound hp_mem.2 h))

#print axioms jsp_000595
#print axioms jsp_000595_least_k2
