/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000836 — Observation record: seven consecutive integers 17..23 with
pairwise distinct totient values.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000836):
  "How long a consecutive-integer interval can have pairwise distinct
   totient values?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of a lower-bound
witness for the catalog question: there exist 7 consecutive integers,
namely 17, 18, 19, 20, 21, 22, 23, whose Euler totient values `Nat.totient`
are pairwise distinct:
  φ(17) = 16, φ(18) = 6, φ(19) = 18, φ(20) = 8,
  φ(21) = 12, φ(22) = 10, φ(23) = 22.

It does NOT determine the maximal length of such a run, does not address
whether that length is unbounded, does not resolve the catalogued open
problem (which remains Open), and makes no award claim. This phenomenon is
complementary to the collision phenomenon recorded in JSP-000835
(φ(15) = φ(16) = 8, awards PR #899): there a short interval forces a
repeated totient, here a short interval has all totients distinct.

Mathematical area: Number theory.
Problem posed: no later than 1985 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **Lower-bound witness for JSP-000836.**

There exist `7` consecutive integers whose totient values are pairwise
distinct: the interval `[17, 23]`, with
`φ(17) = 16, φ(18) = 6, φ(19) = 18, φ(20) = 8, φ(21) = 12, φ(22) = 10,
φ(23) = 22`. -/
theorem jsp000836 : ∃ (a k : ℕ), 7 ≤ k ∧
    ∀ i < k, ∀ j < k, i ≠ j → Nat.totient (a + i) ≠ Nat.totient (a + j) :=
  ⟨17, 7, by decide, by decide⟩

/-- Equivalent finite-range formulation: within `Finset.Icc 17 23` all
totient values of distinct elements differ. -/
theorem jsp000836' : ∀ i ∈ Finset.Icc 17 23, ∀ j ∈ Finset.Icc 17 23,
    i ≠ j → Nat.totient i ≠ Nat.totient j := by
  decide

#print axioms jsp000836
#print axioms jsp000836'
