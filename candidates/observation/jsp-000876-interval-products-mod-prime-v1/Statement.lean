/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000876 — Observation record: two disjoint consecutive-integer intervals
whose products are congruent to one modulo the same prime.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000876):
  "Can several consecutive integer intervals each have product congruent to
   one modulo the same prime?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the explicit
instance `p = 11` with the two *disjoint* consecutive-integer intervals
`[3, 4]` and `[5, 7]`:

- the product of the elements of `[3, 4]` is `3 * 4 = 12 ≡ 1 (mod 11)`;
- the product of the elements of `[5, 7]` is `5 * 6 * 7 = 210 ≡ 1 (mod 11)`;
- the intervals are disjoint since `4 < 5`.

This witnesses the lower bound "several = at least two" for the catalog
question.

It does NOT address how many such disjoint intervals can exist for a fixed
prime (nor arbitrarily many / infinitely many intervals), does not resolve
the catalogued open problem (which remains Open), and makes no award claim.

Mathematical area: Number theory.
Problem posed: no later than 2004 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
Released under the Apache 2.0 license (see the LICENSE file).
-/

import Mathlib

/-- **`11` is prime.** -/
theorem prime_11 : Nat.Prime 11 := by decide

/-- **Interval `[3, 4]` has product `1` mod `11`.**

The product of the consecutive integers `3` and `4` is `12`, and
`12 % 11 = 1`. -/
theorem prod_interval_3_4 : (∏ i ∈ Finset.Icc 3 4, i) % 11 = 1 := by decide

/-- **Interval `[5, 7]` has product `1` mod `11`.**

The product of the consecutive integers `5`, `6`, `7` is `210`, and
`210 % 11 = 1`. -/
theorem prod_interval_5_7 : (∏ i ∈ Finset.Icc 5 7, i) % 11 = 1 := by decide

/-- **Explicit witness for JSP-000876 (lower bound "at least two intervals").**

There exists a prime `p` (namely `11`) admitting two *disjoint*
consecutive-integer intervals (namely `[3, 4]` and `[5, 7]`) such that the
product of the elements of each interval is congruent to `1` modulo `p`:

```lean
⟨11, 3, 4, 5, 7, _, _, _, _, _, _⟩ : ∃ p a₁ b₁ a₂ b₂ : ℕ,
  Nat.Prime p ∧ a₁ ≤ b₁ ∧ b₁ < a₂ ∧ a₂ ≤ b₂ ∧
    (∏ i ∈ Finset.Icc a₁ b₁, i) % p = 1 ∧
    (∏ i ∈ Finset.Icc a₂ b₂, i) % p = 1
```

This is only the instance `p = 11` with two disjoint intervals; the general
question of how many such intervals can exist is untouched. -/
theorem jsp000876 :
    ∃ (p a₁ b₁ a₂ b₂ : ℕ), Nat.Prime p ∧ a₁ ≤ b₁ ∧ b₁ < a₂ ∧ a₂ ≤ b₂ ∧
      (∏ i ∈ Finset.Icc a₁ b₁, i) % p = 1 ∧
      (∏ i ∈ Finset.Icc a₂ b₂, i) % p = 1 :=
  ⟨11, 3, 4, 5, 7, prime_11, by decide, by decide, by decide,
    prod_interval_3_4, prod_interval_5_7⟩

-- Axiom audit: each `decide`-proved component theorem is axiom-free, and the
-- main theorem is assembled purely from those.
#print axioms prime_11
#print axioms prod_interval_3_4
#print axioms prod_interval_5_7
#print axioms jsp000876
