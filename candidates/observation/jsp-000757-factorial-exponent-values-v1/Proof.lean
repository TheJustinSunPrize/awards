/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000757 — Observation record: distinct exponent values in the prime
factorization of `10!`.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0701-0800.md,
#JSP-000757):
  "How many distinct exponent values occur in the prime factorization of
   a factorial?" (Number theory / Factorials; Open.)

Scope of this file
------------------
This file records a complete, machine-checked Lean proof for the exact
instance `n = 10` of the catalog question: `10! = 3628800 = 2^8 * 3^4 *
5^2 * 7`, so the multiset of prime-factor exponents of `10!` is
`{8, 4, 2, 1}` — exactly **four** distinct exponent values.

The main theorem `jsp000757` states that there is a finite set `V` of
cardinality `4`, namely `{8, 4, 2, 1}`, such that for *every* prime `p`:
if `p ∣ 10!` then `expo p ∈ V`, `p ^ expo p ∣ 10!` and `p ^ (expo p + 1) ∤
10!` (i.e. `expo p` is exactly the exponent of `p` in `10!`); and if
`p ∤ 10!` then `expo p = 0`.

It does NOT address the question for general factorials `n!` (the
distribution of the number of distinct exponent values as `n` grows), does
not resolve the catalogued open problem, and makes no award claim.

Method: to keep the kernel work elementary (in particular, no kernel
factorization of `3628800` via `Nat.factorization`), the exponent function
`expo` is defined explicitly by an `if`-chain on `p ∈ {2, 3, 5, 7}`, the
four primes `≤ 10`.  The universal statement over primes `p` is reduced,
via `Nat.Prime.dvd_factorial` (`p ∣ n! ↔ p ≤ n` for `p` prime), to the
finitely many primes `2, 3, 5, 7 ≤ 10`, each discharged by `decide` on
small concrete divisibility facts about `3628800`.

Mathematical area: Number theory / Factorials.
Problem posed: no later than 1982 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- The exponent of `p` in the prime factorization of `10!`, defined
explicitly: `2 ↦ 8`, `3 ↦ 4`, `5 ↦ 2`, `7 ↦ 1`, and `0` for every other
prime. -/
def expo (p : ℕ) : ℕ :=
  if p = 2 then 8 else if p = 3 then 4 else if p = 5 then 2 else if p = 7 then 1 else 0

/-- **JSP-000757, instance `n = 10`.**

The set of exponent values occurring in the prime factorization of `10!`
has cardinality exactly `4` — it is `{8, 4, 2, 1}`:

* `10! = 3628800 = 2^8 * 3^4 * 5^2 * 7^1`, and for each of the four primes
  `p ∈ {2, 3, 5, 7}` the value `expo p` is exactly the exponent of `p` in
  `10!` (so `p ^ expo p ∣ 10!` but `p ^ (expo p + 1) ∤ 10!`);
* every prime `p ∤ 10!` has `expo p = 0`.

Hence exactly four distinct exponent values (`8, 4, 2, 1`) occur in the
prime factorization of `10!`. -/
theorem jsp000757 : ∃ (V : Finset ℕ), V.card = 4 ∧ V = {8, 4, 2, 1} ∧
    ∀ p : ℕ, Nat.Prime p → ((p ∣ Nat.factorial 10 → expo p ∈ V ∧ p ^ expo p ∣ Nat.factorial 10 ∧
        ¬ p ^ (expo p + 1) ∣ Nat.factorial 10) ∧ (¬ p ∣ Nat.factorial 10 → expo p = 0)) := by
  refine ⟨{8, 4, 2, 1}, by decide, rfl, fun p hp => ?_⟩
  constructor
  · -- if `p` divides `10!` then `p` is one of the four primes `2, 3, 5, 7 ≤ 10`
    intro hdvd
    have hp10 : p ≤ 10 :=
      (Nat.Prime.dvd_factorial hp).mp hdvd
    interval_cases p
    · exact absurd hp (by norm_num) -- p = 0
    · exact absurd hp (by norm_num) -- p = 1
    · exact ⟨by decide, by decide, by decide⟩ -- p = 2
    · exact ⟨by decide, by decide, by decide⟩ -- p = 3
    · exact absurd hp (by norm_num) -- p = 4
    · exact ⟨by decide, by decide, by decide⟩ -- p = 5
    · exact absurd hp (by norm_num) -- p = 6
    · exact ⟨by decide, by decide, by decide⟩ -- p = 7
    · exact absurd hp (by norm_num) -- p = 8
    · exact absurd hp (by norm_num) -- p = 9
    · exact absurd hp (by norm_num) -- p = 10
  · -- if `p` does not divide `10!` then `p` is none of `2, 3, 5, 7`
    intro hndvd
    simp only [expo]
    split_ifs with h2 h3 h5 h7
    · exact absurd (h2 ▸ (by norm_num : (2:ℕ) ∣ Nat.factorial 10)) hndvd
    · exact absurd (h3 ▸ (by norm_num : (3:ℕ) ∣ Nat.factorial 10)) hndvd
    · exact absurd (h5 ▸ (by norm_num : (5:ℕ) ∣ Nat.factorial 10)) hndvd
    · exact absurd (h7 ▸ (by norm_num : (7:ℕ) ∣ Nat.factorial 10)) hndvd
    · rfl

#print axioms jsp000757
