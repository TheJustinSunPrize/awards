import Mathlib

/-- The largest prime factor of `n`, defined as `0` for `n < 2`. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactors.sup id

namespace Jsp000307

/-- For prime `p`, `maxPrimeFac p = p`. -/
theorem maxPrimeFac_prime {p : ℕ} (hp : p.Prime) : maxPrimeFac p = p := by
  apply le_antisymm
  · rw [maxPrimeFac, Finset.sup_le_iff]
    intro b hb
    rw [Nat.mem_primeFactors] at hb
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hb.2.2) hb.2.1
  · rw [maxPrimeFac]
    apply Finset.le_sup (s := Nat.primeFactors p) (f := id) (b := p)
    rw [Nat.mem_primeFactors]
    exact ⟨hp, dvd_refl p, hp.ne_zero⟩

/-- For primes `a ≤ b`, `maxPrimeFac (a * b) = b`. -/
theorem maxPrimeFac_mul_prime {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≤ b) :
    maxPrimeFac (a * b) = b := by
  apply le_antisymm
  · rw [maxPrimeFac, Finset.sup_le_iff]
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqd, _⟩ := hq
    simp only [id_eq]
    rcases hqp.dvd_mul.mp hqd with h | h
    · rcases (Nat.dvd_prime ha).mp h with h' | h'
      · exact absurd h' hqp.ne_one
      · exact h' ▸ hab
    · rcases (Nat.dvd_prime hb).mp h with h' | h'
      · exact absurd h' hqp.ne_one
      · exact h' ▸ le_refl b
  · rw [maxPrimeFac]
    apply Finset.le_sup (s := Nat.primeFactors (a * b)) (f := id) (b := b)
    rw [Nat.mem_primeFactors]
    exact ⟨hb, ⟨a, by ring⟩, mul_ne_zero ha.ne_zero hb.ne_zero⟩

/-- If `n` is odd, divisible by `3`, and at least `9`, then every prime
factor `q` of `n` satisfies `q ≤ n / 3`: writing `n = q * k`, we have
`k ≥ 2` (else `n` would be prime, contradicting `3 ∣ n` and `9 ≤ n`),
and `k ≠ 2` (else `n` would be even). -/
theorem maxPrimeFac_le_third {n : ℕ} (hodd : n % 2 = 1) (h3 : 3 ∣ n) (h9 : 9 ≤ n) :
    maxPrimeFac n ≤ n / 3 := by
  have hnnp : ¬n.Prime := fun hnp => by
    have h3n : 3 = n := by
      rcases (Nat.dvd_prime hnp).mp h3 with h | h
      · exact absurd h (by decide)
      · exact h
    omega
  rw [maxPrimeFac, Finset.sup_le_iff]
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqp, hqd, hn0⟩ := hq
  simp only [id_eq]
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
  -- goal: q * 3 ≤ n
  have hkey : q * (n / q) = n := by
    rw [mul_comm]; exact Nat.div_mul_cancel hqd
  have hqn : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqd
  have hk2 : 2 ≤ n / q := by
    have hpos : 1 ≤ n / q := Nat.div_pos hqn hqp.pos
    have hne : n / q ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hkey
      exact absurd (hkey ▸ hqp) hnnp
    omega
  have hk3 : 3 ≤ n / q := by
    have hne : n / q ≠ 2 := by
      intro h2
      rw [h2] at hkey
      have heven : 2 ∣ n := ⟨q, by omega⟩
      rw [Nat.dvd_iff_mod_eq_zero] at heven
      omega
    omega
  calc q * 3 ≤ q * (n / q) := Nat.mul_le_mul_left q hk3
    _ = n := hkey

theorem maxPrimeFac_thirteen : maxPrimeFac 13 = 13 :=
  maxPrimeFac_prime (by decide)

theorem maxPrimeFac_fourteen : maxPrimeFac 14 = 7 :=
  maxPrimeFac_mul_prime (a := 2) (b := 7) (by decide) (by decide) (by norm_num)

theorem maxPrimeFac_fifteen : maxPrimeFac 15 = 5 :=
  maxPrimeFac_mul_prime (a := 3) (b := 5) (by decide) (by decide) (by norm_num)

/-- **JSP-000307.** Three consecutive integers can have strictly decreasing
largest prime factors.

Witness `n = 13`: `maxPrimeFac 13 = 13`, `maxPrimeFac 14 = 7`,
`maxPrimeFac 15 = 5`, and `13 > 7 > 5`.

This resolves the existential question (the answer is yes). The theorem
that infinitely many such triples exist (Erdős–Pomerance, Balasubramanian)
is outside the scope of this formalization. -/
theorem jsp_000307 : ∃ n : ℕ, 1 < n ∧
    maxPrimeFac n > maxPrimeFac (n + 1) ∧
    maxPrimeFac (n + 1) > maxPrimeFac (n + 2) :=
  ⟨13, by norm_num,
   by rw [maxPrimeFac_thirteen, maxPrimeFac_fourteen]; norm_num,
   by rw [maxPrimeFac_fourteen, maxPrimeFac_fifteen]; norm_num⟩

/-- **Sufficient condition.** For every prime `p` with `p % 6 = 1` such that
`(p + 1) / 2` is prime, the largest prime factors of `p, p + 1, p + 2` are
strictly decreasing: `maxPrimeFac p = p`, `maxPrimeFac (p + 1) = (p + 1) / 2`,
and `maxPrimeFac (p + 2) ≤ (p + 2) / 3 < (p + 1) / 2 < p`.

This is a strict strengthening of the usual sufficient condition: unlike
the condition that `(p + 2) / 3` be prime as well, the bound
`maxPrimeFac (p + 2) ≤ (p + 2) / 3` needs only that `p + 2` is odd and
divisible by `3`. For example, `p = 277` has `(p + 2) / 3 = 93` composite
yet still yields the decreasing triple `277 > 139 > 31`. -/
theorem jsp_000307_family {p : ℕ} (hp : p.Prime) (hmod : p % 6 = 1)
    (hq : ((p + 1) / 2).Prime) :
    maxPrimeFac p > maxPrimeFac (p + 1) ∧
    maxPrimeFac (p + 1) > maxPrimeFac (p + 2) := by
  have hp7 : 7 ≤ p := by
    by_contra h
    simp only [not_le] at h
    interval_cases p <;> first
      | exact absurd hp (by decide)
      | exact absurd hmod (by decide)
  set q := (p + 1) / 2 with hqdef
  have hpodd : p % 2 = 1 := by omega
  have h2p1 : 2 * q = p + 1 := by
    have hmod2 : (p + 1) % 2 = 0 := by omega
    have hda := Nat.div_add_mod (p + 1) 2
    omega
  have h1 : maxPrimeFac p = p := maxPrimeFac_prime hp
  have hq2 : 2 < q := by omega
  have h2 : maxPrimeFac (p + 1) = q := by
    rw [← h2p1]
    exact maxPrimeFac_mul_prime (by decide) hq hq2.le
  have h3 : maxPrimeFac (p + 2) ≤ (p + 2) / 3 :=
    maxPrimeFac_le_third (by omega) (by omega) (by omega)
  rw [h1, h2]
  refine ⟨by omega, lt_of_le_of_lt h3 (by omega)⟩

/-- The witness `p = 13` satisfies the sufficient condition. -/
theorem jsp_000307_witness :
    maxPrimeFac 13 > maxPrimeFac 14 ∧ maxPrimeFac 14 > maxPrimeFac 15 :=
  jsp_000307_family (by decide) (by decide) (by decide)

/-- `p = 277`: `(p + 2) / 3 = 93` is composite, so this case is not covered
by the sufficient condition that additionally requires `(p + 2) / 3` prime. -/
theorem jsp_000307_family_277 :
    maxPrimeFac 277 > maxPrimeFac 278 ∧ maxPrimeFac 278 > maxPrimeFac 279 :=
  jsp_000307_family (by norm_num) (by decide) (by norm_num)

end Jsp000307

#print axioms Jsp000307.jsp_000307
#print axioms Jsp000307.jsp_000307_family
