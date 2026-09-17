/-
JSP-000307: Can three consecutive integers have strictly decreasing (or
increasing) largest prime factors?

Answer: Yes. Balasubramanian (2001) proved that infinitely many such triples
exist in both directions.

This file formalizes two complete conditional theorems providing explicit
infinite families:

1. **Decreasing**: For every prime p with p % 6 = 1 such that (p+1)/2 and
   (p+2)/3 are also prime, the largest prime factors of (p, p+1, p+2) are
   strictly decreasing.

2. **Increasing**: For every prime q > 3 such that (3q+1)/2 and 3q+2 are
   also prime, the largest prime factors of (3q, 3q+1, 3q+2) are strictly
   increasing.

Both proofs use exact factorizations and elementary inequalities.

The first few examples for the decreasing case:
  p = 13, 37, 157, 541, 877, 1201, ...

The first few examples for the increasing case:
  q = 7, 19, 59, 127, 167, 239, 439, 479, 607, 859, ...

References:
  [ErPo78] Erdős and Pomerance, "On the largest prime factors of n and n+1",
           Aequationes Math. 16 (1978), 311–321.
  [Ba01]   Balasubramanian, "On triplets with descending largest prime factors",
           Studia Sci. Math. Hungar. 36 (2001), 45–50.
-/

import Mathlib

open Nat

/-- JSP-000307 (Decreasing): For every prime p with p % 6 = 1 such that
(p+1)/2 and (p+2)/3 are also prime, the largest prime factors of
(p, p+1, p+2) are strictly decreasing. -/
theorem jsp_000307_decreasing (p : ℕ)
    (hp : p.Prime)
    (hp_mod : p % 6 = 1)
    (hq : ((p + 1) / 2).Prime)
    (hr : ((p + 2) / 3).Prime) :
    maxPrimeFac p > maxPrimeFac (p + 1) ∧
    maxPrimeFac (p + 1) > maxPrimeFac (p + 2) := by
  -- p ≥ 7 since p is prime and p % 6 = 1
  have hp_ge7 : p ≥ 7 := by
    by_contra h
    have hlt : p < 7 := by omega
    have : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp_mod (by decide)
    · exact absurd hp_mod (by decide)
    · exact absurd hp_mod (by decide)
    · exact absurd hp_mod (by decide)
    · exact absurd hp_mod (by decide)
  -- p % 2 = 1
  have hp_odd : p % 2 = 1 := by
    have h6 : 6 * (p / 6) + p % 6 = p := Nat.div_add_mod p 6
    rw [hp_mod] at h6
    omega
  -- p + 1 = 2 * ((p+1)/2)
  have hp1_fact : p + 1 = 2 * ((p + 1) / 2) := by
    have h := Nat.div_add_mod (p + 1) 2
    have : (p + 1) % 2 = 0 := by omega
    rw [this] at h
    omega
  -- p + 2 = 3 * ((p+2)/3)
  have hp2_mod3 : (p + 2) % 3 = 0 := by
    have h6 : 6 * (p / 6) + p % 6 = p := Nat.div_add_mod p 6
    rw [hp_mod] at h6
    have key : p + 2 = 3 * (2 * (p / 6) + 1) := by omega
    rw [key]
    exact Nat.mod_eq_zero_of_dvd ⟨2 * (p / 6) + 1, rfl⟩
  have hp2_fact : p + 2 = 3 * ((p + 2) / 3) := by
    have h := Nat.div_add_mod (p + 2) 3
    rw [hp2_mod3] at h
    omega
  -- p ≥ 13: since p=7 gives (p+1)/2=4, not prime
  have hp_ge13 : p ≥ 13 := by
    by_contra h
    have : p < 13 := by omega
    have : p = 7 := by omega
    rw [this] at hq
    exact absurd hq (by decide)
  -- lpf(p) = p
  have h_lpf_p : maxPrimeFac p = p := hp.maxPrimeFac_eq_self
  -- lpf(p+1) = (p+1)/2
  have h_lpf_p1 : maxPrimeFac (p + 1) = (p + 1) / 2 := by
    rw [hp1_fact, maxPrimeFac_mul two_ne_zero (by omega)]
    rw [(Nat.prime_two).maxPrimeFac_eq_self, hq.maxPrimeFac_eq_self]
    omega
  -- lpf(p+2) = (p+2)/3
  have h_lpf_p2 : maxPrimeFac (p + 2) = (p + 2) / 3 := by
    rw [hp2_fact, maxPrimeFac_mul (by decide : (3:ℕ) ≠ 0) (by omega)]
    rw [(by decide : (3:ℕ).Prime).maxPrimeFac_eq_self, hr.maxPrimeFac_eq_self]
    omega
  -- Final: p > (p+1)/2 > (p+2)/3
  rw [h_lpf_p, h_lpf_p1, h_lpf_p2]
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-- JSP-000307 (Increasing): For every prime q > 3 such that (3q+1)/2 and
3q+2 are also prime, the largest prime factors of (3q, 3q+1, 3q+2) are
strictly increasing. -/
theorem jsp_000307_increasing (q : ℕ)
    (hq : q.Prime)
    (hq_gt3 : q > 3)
    (hp : ((3 * q + 1) / 2).Prime)
    (hr : (3 * q + 2).Prime) :
    maxPrimeFac (3 * q) < maxPrimeFac (3 * q + 1) ∧
    maxPrimeFac (3 * q + 1) < maxPrimeFac (3 * q + 2) := by
  -- lpf(3*q) = q (since 3*q = 3 * q, and q > 3)
  have h_lpf_n : maxPrimeFac (3 * q) = q := by
    rw [maxPrimeFac_mul (by decide : (3:ℕ) ≠ 0) (by omega)]
    rw [(by decide : (3:ℕ).Prime).maxPrimeFac_eq_self, hq.maxPrimeFac_eq_self]
    omega
  -- 3*q+1 = 2 * ((3*q+1)/2)
  have h1_even : (3 * q + 1) % 2 = 0 := by
    have hq_odd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · omega
      · exact h
    omega
  have h1_fact : 3 * q + 1 = 2 * ((3 * q + 1) / 2) := by
    have h := Nat.div_add_mod (3 * q + 1) 2
    rw [h1_even] at h
    omega
  have h_lpf_n1 : maxPrimeFac (3 * q + 1) = (3 * q + 1) / 2 := by
    rw [h1_fact, maxPrimeFac_mul two_ne_zero (by omega)]
    rw [(Nat.prime_two).maxPrimeFac_eq_self, hp.maxPrimeFac_eq_self]
    have : (3 * q + 1) / 2 > 2 := by omega
    omega
  -- lpf(3*q+2) = 3*q+2 (since it's prime)
  have h_lpf_n2 : maxPrimeFac (3 * q + 2) = 3 * q + 2 := hr.maxPrimeFac_eq_self
  -- Final: q < (3*q+1)/2 < 3*q+2
  rw [h_lpf_n, h_lpf_n1, h_lpf_n2]
  refine ⟨?_, ?_⟩
  · omega
  · omega
