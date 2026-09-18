/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000317 — Observation record: a prime square followed by two consecutive
integers having no prime factor larger than that prime.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0301-0400.md,
#JSP-000317):
  "Can a prime square be followed by several consecutive integers having no
   prime factor larger than that prime?"
  (Mathematical area: Number theory; status: Open; Lean proof: No.)

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the literal
length-two existence component of the catalog question: there exists a
prime `p` such that both `p^2 + 1` and `p^2 + 2` have all their prime
factors at most `p`.  The witness is `p = 41`:

  * `41^2 + 1 = 1682 = 2 * 29^2`      — every prime divisor (`2`, `29`) ≤ 41;
  * `41^2 + 2 = 1683 = 3^2 * 11 * 17` — every prime divisor (`3`, `11`,
    `17`) ≤ 41.

Two further small witnesses are included as auxiliary evidence that this
is not an isolated accident:

  * `p = 157`:  `157^2 + 1 = 24650 = 2 * 5^2 * 17 * 29`,
                `157^2 + 2 = 24651 = 3^3 * 11 * 83`;
  * `p = 211`:  `211^2 + 1 = 44522 = 2 * 113 * 197`,
                `211^2 + 2 = 44523 = 3^3 * 17 * 97`.

It does NOT address how long such a run of consecutive integers after a
prime square can be, does not resolve the catalogued open problem (which
remains **Open**), and makes no award claim.

Mathematical area: Number theory.
Problem posed: no later than 1980 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).

Proof notes
-----------
* Divisor bounds are obtained from explicit factorizations of the two
  integers after `p^2` (e.g. `1682 = 2 * (29 * 29)`) via
  `Nat.Prime.dvd_mul` (a prime dividing a product divides a factor) and
  `Nat.dvd_prime` (`m ∣ p ↔ m = 1 ∨ m = p` for `p` prime), finishing each
  case with `omega`.  The two helper lemmas
  `jsp000317_dvd_mul` / `jsp000317_dvd_prime` wrap these API entry points.
* This explicit-factorization route avoids kernel reduction of
  `Nat.primeFactorsList` (well-founded recursion) and of primality
  deciders on the composite integers themselves.
* `set_option maxRecDepth 8000` is set because the `decide` call proving
  `Nat.Prime 211` exceeds the default recursion depth on this toolchain.
  All other `decide` uses are on small numerals.
-/

import Mathlib

set_option maxRecDepth 8000

/-- A prime factor of a prime `n` is `1` or `n` (wrapper around
`Nat.dvd_prime`). -/
theorem jsp000317_dvd_prime {q n : ℕ} (h : q ∣ n) (hn : Nat.Prime n) :
    q = 1 ∨ q = n := (Nat.dvd_prime hn).mp h

/-- A prime dividing a product divides one factor (wrapper around
`Nat.Prime.dvd_mul`). -/
theorem jsp000317_dvd_mul {q m n : ℕ} (hq : Nat.Prime q) (h : q ∣ m * n) :
    q ∣ m ∨ q ∣ n := (hq.dvd_mul).mp h

/-- Every prime divisor of `1682 = 41^2 + 1 = 2 * 29^2` is at most `41`. -/
theorem jsp000317_dvd_1682 : ∀ q : ℕ, Nat.Prime q → q ∣ 1682 → q ≤ 41 := by
  intro q hq hdvd
  have he : (1682 : ℕ) = 2 * (29 * 29) := by norm_num
  rw [he] at hdvd
  rcases jsp000317_dvd_mul hq hdvd with h | h
  · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
  · rcases jsp000317_dvd_mul hq h with h | h <;>
      rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega

/-- Every prime divisor of `1683 = 41^2 + 2 = 3^2 * 11 * 17` is at most
`41`. -/
theorem jsp000317_dvd_1683 : ∀ q : ℕ, Nat.Prime q → q ∣ 1683 → q ≤ 41 := by
  intro q hq hdvd
  have he : (1683 : ℕ) = 3 * (3 * (11 * 17)) := by norm_num
  rw [he] at hdvd
  rcases jsp000317_dvd_mul hq hdvd with h | h
  · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
  · rcases jsp000317_dvd_mul hq h with h | h
    · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
    · rcases jsp000317_dvd_mul hq h with h | h <;>
        rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega

/-- Main observation (JSP-000317, length-two component): there exists a
prime `p` such that both integers immediately following `p^2` have no
prime factor larger than `p`. -/
theorem jsp000317 : ∃ p : ℕ, Nat.Prime p ∧
    (∀ q, Nat.Prime q → q ∣ p ^ 2 + 1 → q ≤ p) ∧
    (∀ q, Nat.Prime q → q ∣ p ^ 2 + 2 → q ≤ p) := by
  refine ⟨41, by decide, ?_, ?_⟩
  · intro q hq hq41
    have he : (41 : ℕ) ^ 2 + 1 = 1682 := by norm_num
    rw [he] at hq41
    exact jsp000317_dvd_1682 q hq hq41
  · intro q hq hq41
    have he : (41 : ℕ) ^ 2 + 2 = 1683 := by norm_num
    rw [he] at hq41
    exact jsp000317_dvd_1683 q hq hq41

/-- Auxiliary witness `p = 157`: both `157^2 + 1 = 24650 = 2 * 5^2 * 17 * 29`
and `157^2 + 2 = 24651 = 3^3 * 11 * 83` have all prime factors at most
`157`. -/
theorem jsp000317_witness_157 : Nat.Prime 157 ∧
    (∀ q, Nat.Prime q → q ∣ 157 ^ 2 + 1 → q ≤ 157) ∧
    (∀ q, Nat.Prime q → q ∣ 157 ^ 2 + 2 → q ≤ 157) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro q hq hq157
    have he : (157 : ℕ) ^ 2 + 1 = 2 * (5 * (5 * (17 * 29))) := by norm_num
    rw [he] at hq157
    rcases jsp000317_dvd_mul hq hq157 with h | h
    · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
    · rcases jsp000317_dvd_mul hq h with h | h
      · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
      · rcases jsp000317_dvd_mul hq h with h | h
        · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
        · rcases jsp000317_dvd_mul hq h with h | h <;>
            rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
  · intro q hq hq157
    have he : (157 : ℕ) ^ 2 + 2 = 3 * (3 * (3 * (11 * 83))) := by norm_num
    rw [he] at hq157
    rcases jsp000317_dvd_mul hq hq157 with h | h
    · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
    · rcases jsp000317_dvd_mul hq h with h | h
      · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
      · rcases jsp000317_dvd_mul hq h with h | h
        · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
        · rcases jsp000317_dvd_mul hq h with h | h <;>
            rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega

/-- Auxiliary witness `p = 211`: both `211^2 + 1 = 44522 = 2 * 113 * 197`
and `211^2 + 2 = 44523 = 3^3 * 17 * 97` have all prime factors at most
`211`. -/
theorem jsp000317_witness_211 : Nat.Prime 211 ∧
    (∀ q, Nat.Prime q → q ∣ 211 ^ 2 + 1 → q ≤ 211) ∧
    (∀ q, Nat.Prime q → q ∣ 211 ^ 2 + 2 → q ≤ 211) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro q hq hq211
    have he : (211 : ℕ) ^ 2 + 1 = 2 * (113 * 197) := by norm_num
    rw [he] at hq211
    rcases jsp000317_dvd_mul hq hq211 with h | h
    · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
    · rcases jsp000317_dvd_mul hq h with h | h <;>
        rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
  · intro q hq hq211
    have he : (211 : ℕ) ^ 2 + 2 = 3 * (3 * (3 * (17 * 97))) := by norm_num
    rw [he] at hq211
    rcases jsp000317_dvd_mul hq hq211 with h | h
    · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
    · rcases jsp000317_dvd_mul hq h with h | h
      · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
      · rcases jsp000317_dvd_mul hq h with h | h
        · rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega
        · rcases jsp000317_dvd_mul hq h with h | h <;>
            rcases jsp000317_dvd_prime h (by decide) with h' | h' <;> omega

#print axioms jsp000317
#print axioms jsp000317_dvd_1682
#print axioms jsp000317_dvd_1683
#print axioms jsp000317_witness_157
#print axioms jsp000317_witness_211
