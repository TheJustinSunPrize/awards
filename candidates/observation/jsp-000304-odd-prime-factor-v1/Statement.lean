/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
import Mathlib

/-!
# JSP-000304 — Lean formalization observation

**Problem (TheJustinSunPrize/awards, JSP-000304).** *How large a prime factor
must the product of two consecutive positive integers have?* (Number theory;
posed no later than 1965, bibliographic evidence; catalog status: Open,
Lean proof: No.)

**What is proved here (complete answer to the catalog question).**

For every `n ≥ 2` the product `n * (n + 1)` of the two consecutive positive
integers `n` and `n + 1` always has a prime factor at least `3`, and the
guaranteed lower bound `3` is best possible: at `n = 8` the product
`8 * 9 = 72 = 2 ^ 3 * 3 ^ 2` has largest prime factor exactly `3`.

The argument is elementary: of two consecutive integers one is even and the
other is odd, and the odd one is at least `3` (since `n ≥ 2`); every prime
factor of an odd number is odd, hence at least `3`, and it divides the product.

In symbols, the two halves proved here are:

```text
jsp000304:        ∀ n ≥ 2, ∃ p, Nat.Prime p ∧ 3 ≤ p ∧ p ∣ n * (n + 1)
jsp000304_tight:  ∃ n ≥ 2, ∀ p, Nat.Prime p → p ∣ n * (n + 1) → p ≤ 3
```

and `jsp000304_complete` records them together as a single statement: the
guaranteed lower bound on the largest prime factor of `n * (n + 1)` (over
`n ≥ 2`) is exactly `3`.

**Scope of this file (honest, scoped observation).** The catalog entry for
JSP-000304 is marked Open; this file gives a complete, machine-checked answer
to the catalog question as stated ("how large a prime factor must the product
of two consecutive positive integers have?") with the optimal constant `3` in
the range `n ≥ 2`. Whether the catalog entry should be reclassified is a
decision for the maintainers; this file is submitted as a formalization
observation only and makes no claim on any award.

## Provenance / toolchain

* Lean `v4.35.0-rc2`, Mathlib `v4.35.0-rc2` (pinned in `lean-toolchain`).
* No `sorry`, `admit`, `native_decide`, or unproven assumptions are used;
  `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`
  for each theorem below.
-/

/-- **JSP-000304, main observation.** For `n ≥ 2`, the product `n * (n + 1)`
of two consecutive positive integers always has a prime factor `p ≥ 3`:
one of `n`, `n + 1` is odd and at least `3`, and any prime factor of that
odd number is an odd prime, hence at least `3`, and divides the product. -/
theorem jsp000304 (n : ℕ) (hn : 2 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ 3 ≤ p ∧ p ∣ n * (n + 1) := by
  -- One of `n`, `n + 1` is odd and at least `3`.
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have key : ∃ m : ℕ, m ∣ n * (n + 1) ∧ m % 2 = 1 ∧ 3 ≤ m := by
    rcases hmod with hn2 | hn2
    · -- `n` is even, so `n + 1` is odd and `3 ≤ n + 1`
      exact ⟨n + 1, ⟨n, Nat.mul_comm n (n + 1)⟩, by omega, by omega⟩
    · -- `n` itself is odd, and `2 ≤ n` odd forces `3 ≤ n`
      exact ⟨n, ⟨n + 1, rfl⟩, by omega, by omega⟩
  obtain ⟨m, hmdvd, hm1, hm3⟩ := key
  -- An odd number `≥ 3` has a prime factor.
  have hmne : m ≠ 1 := by omega
  obtain ⟨p, hp, hpm⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hmne
  have h2p : 2 ≤ p := hp.two_le
  -- That prime factor is odd (it divides an odd number), hence `≥ 3`.
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    obtain ⟨j, hj⟩ := hpm
    omega
  exact ⟨p, hp, by omega, Nat.dvd_trans hpm hmdvd⟩

/-- **Auxiliary for `jsp000304_tight`.** Every prime factor of
`72 = 8 * 9 = 2 ^ 3 * 3 ^ 2` is at most `3`. -/
theorem prime_dvd_72_le_three {p : ℕ} (hp : Nat.Prime p) (h72 : p ∣ 72) : p ≤ 3 := by
  rw [show (72 : ℕ) = 8 * 9 from rfl] at h72
  rcases (hp.dvd_mul).1 h72 with h | h
  · rw [show (8 : ℕ) = 2 * 4 from rfl] at h
    rcases (hp.dvd_mul).1 h with h | h
    · exact (Nat.le_of_dvd (by decide) h).trans (by decide)
    · rw [show (4 : ℕ) = 2 * 2 from rfl] at h
      rcases (hp.dvd_mul).1 h with h | h
      · exact (Nat.le_of_dvd (by decide) h).trans (by decide)
      · exact (Nat.le_of_dvd (by decide) h).trans (by decide)
  · rw [show (9 : ℕ) = 3 * 3 from rfl] at h
    rcases (hp.dvd_mul).1 h with h | h
    · exact Nat.le_of_dvd (by decide) h
    · exact Nat.le_of_dvd (by decide) h

/-- **JSP-000304, tightness.** The bound `3` in `jsp000304` is optimal: at
`n = 8` the product `8 * 9 = 72` has all prime factors `≤ 3`, so no
guaranteed lower bound larger than `3` is possible. -/
theorem jsp000304_tight :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ p, Nat.Prime p → p ∣ n * (n + 1) → p ≤ 3 :=
  ⟨8, by decide, fun _ hp hdvd => prime_dvd_72_le_three hp hdvd⟩

/-- **JSP-000304, complete answer.** Over `n ≥ 2`, the guaranteed lower bound
for a prime factor of the product of two consecutive positive integers is
exactly `3`: it is always at least `3`, and `3` is attained (at `n = 8`). -/
theorem jsp000304_complete :
    (∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ 3 ≤ p ∧ p ∣ n * (n + 1)) ∧
      ∃ n : ℕ, 2 ≤ n ∧ ∀ p, Nat.Prime p → p ∣ n * (n + 1) → p ≤ 3 :=
  ⟨jsp000304, jsp000304_tight⟩

-- Axiom audit
#print axioms jsp000304
#print axioms prime_dvd_72_le_three
#print axioms jsp000304_tight
#print axioms jsp000304_complete
