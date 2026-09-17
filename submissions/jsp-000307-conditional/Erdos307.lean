/-
JSP-000307: Can three consecutive integers have strictly decreasing largest
prime factors?

Answer: Yes. Balasubramanian (2001) proved that infinitely many such triples
exist.

This file formalizes a complete conditional theorem: for every prime p with
p % 6 = 1 such that (p+1)/2 and (p+2)/3 are also prime, the largest prime
factors of (p, p+1, p+2) are strictly decreasing.

The first few examples are p = 13, 37, 157, 541, 877, 1201, ...

References:
  [ErPo78] Erdős and Pomerance, Aequationes Math. 16 (1978), 311–321.
  [Ba01]   Balasubramanian, Studia Sci. Math. Hungar. 36 (2001), 45–50.
-/

import Mathlib

open Nat

theorem jsp_000307_conditional (p : ℕ)
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
  -- First prove (p+2) % 3 = 0
  have hp2_mod3 : (p + 2) % 3 = 0 := by
    -- p = 6*(p/6) + 1, so p + 2 = 6*(p/6) + 3 = 3*(2*(p/6) + 1)
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
