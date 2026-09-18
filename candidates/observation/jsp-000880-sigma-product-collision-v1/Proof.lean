/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000880 — Observation record: explicit collision for `n` times its
divisor sum.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000880):
  "How many integers can have a prescribed value of the integer times its
   divisor sum?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the existence
component of an observation about the catalogued open question: some
integers `m` have at least two distinct preimages under `n ↦ n * σ(n)`,
where `σ` is the sum-of-divisors function. The explicit collision is
`12 * σ(12) = 14 * σ(14) = 336` (σ(12) = 1+2+3+4+6+12 = 28 and
σ(14) = 1+2+7+14 = 24).

It does NOT answer the catalogued question itself (how many `n` can share a
prescribed value of `n * σ(n)`, whether that multiplicity is unbounded,
etc.), does not resolve the catalogued open problem, and makes no award
claim.

Mathematical area: Number theory.
Problem posed: no later than 2004 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **JSP-000880 observation (existence component).**

There exist distinct natural numbers `a` and `b` and a value `m` with
`a * σ(a) = b * σ(b) = m`: the collision `12 * σ(12) = 14 * σ(14) = 336`.
Here `σ` is Mathlib's `ArithmeticFunction.sigma`:
`ArithmeticFunction.sigma k n = ∑ d ∈ n.divisors, d ^ k`, so
`ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d` is the standard
sum-of-divisors function. -/
theorem jsp000880 :
    ∃ a b m : ℕ, a ≠ b ∧ a * ArithmeticFunction.sigma 1 a = m ∧ b * ArithmeticFunction.sigma 1 b = m :=
  ⟨12, 14, 336, by decide, by decide, by decide⟩

-- Axiom audit (decide proofs are expected to be axiom-free):
#print axioms jsp000880
