import Mathlib

/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-!
# JSP-000566 — Lean formalization observation

Problem (TheJustinSunPrize/awards, JSP-000566):
"How fast can prime chains grow when each prime divides one less than the next?"
(Mathematical area: Number theory; catalog status: Open; Lean proof: No.)

A *prime chain* is a sequence of primes `p1, p2, ...` in which each `pᵢ` divides
`p_{i+1} - 1`.

## What this file proves

The **existential instance only**: there exists a strictly increasing chain of
six primes starting at 2,

`2 → 3 → 7 → 29 → 59 → 709`,

in which each prime divides one less than the next prime:

* `3 - 1 = 1 * 2`
* `7 - 1 = 2 * 3`
* `29 - 1 = 4 * 7`
* `59 - 1 = 2 * 29`
* `709 - 1 = 12 * 59`

All primality and divisibility facts are discharged by `decide` on the literal
numerals; no external hypotheses are used.

## Scope (honest boundary)

This observation covers **only** the existence of this single length-6 chain
starting at 2.  It says nothing about growth rates of arbitrary prime chains,
nor about infinitude of such chains, and it does **not** resolve the open
problem JSP-000566.  No award is claimed.

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

set_option maxRecDepth 8000

/-- An explicit strictly increasing prime chain `2 → 3 → 7 → 29 → 59 → 709`
of length six starting at 2, in which each prime divides one less than the
next.  This is the witness instance for the JSP-000566 observation; it carries
no claim about the open growth-rate question itself. -/
theorem jsp000566 :
    ∃ (a b c d e f : ℕ), Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧
      Nat.Prime d ∧ Nat.Prime e ∧ Nat.Prime f ∧ a ∣ b - 1 ∧ b ∣ c - 1 ∧
      c ∣ d - 1 ∧ d ∣ e - 1 ∧ e ∣ f - 1 ∧ 1 < a ∧ a < b ∧ b < c ∧ c < d ∧
      d < e ∧ e < f :=
  ⟨2, 3, 7, 29, 59, 709, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- The same witness in list form: the list `[2, 3, 7, 29, 59, 709]` has six
entries, every entry is a prime greater than one, and each adjacent pair
satisfies the divides-one-less condition. -/
theorem jsp000566_list :
    ∃ (l : List ℕ), l.length = 6 ∧ l = [2, 3, 7, 29, 59, 709] ∧
      (∀ x ∈ l, Nat.Prime x ∧ 1 < x) ∧
      2 ∣ 3 - 1 ∧ 3 ∣ 7 - 1 ∧ 7 ∣ 29 - 1 ∧ 29 ∣ 59 - 1 ∧ 59 ∣ 709 - 1 :=
  ⟨[2, 3, 7, 29, 59, 709], by decide, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

#print axioms jsp000566
#print axioms jsp000566_list
