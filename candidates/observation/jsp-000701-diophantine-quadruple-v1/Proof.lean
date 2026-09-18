/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000701 — Observation record: a Diophantine quadruple whose pairwise
products plus one all have a nontrivial square factor.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0701-0800.md,
#JSP-000701):
  "How large can an integer-interval subset be if every pairwise product
   plus one has a nontrivial square factor?"

Mathematical area: Number theory.
Problem posed: no later than 1992 (bibliographic evidence).

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of a *constructive
existence component* for the catalog question: the 4-element set
`{1, 3, 8, 120}` (the classical Diophantine quadruple) has the property that
for every two *distinct* elements `a, b` of the set, `a * b + 1` has a
nontrivial square factor, i.e. there is `q > 1` with `q * q ∣ a * b + 1`.
In fact all six pairwise products plus one are perfect squares:
  1*3+1 = 4 = 2^2,  1*8+1 = 9 = 3^2,  1*120+1 = 121 = 11^2,
  3*8+1 = 25 = 5^2, 3*120+1 = 361 = 19^2, 8*120+1 = 961 = 31^2.

Honest boundary of what is proved:
* "Pairwise product" is read in the standard way, as applying to *distinct*
  pairs only. Self-pairs (a = a) are NOT in scope: e.g. 1*1+1 = 2 is
  squarefree, so the self-pair reading would make the property vacuously
  false for any set containing 1.
* This proves only the lower-bound/existence component `|S| >= 4` is
  attainable (for subsets of the positive integers). It does NOT prove any
  upper bound, does not determine the maximum size, and does not resolve the
  catalogued open problem, which remains Open.

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **JSP-000701 observation (existence component, distinct pairs only).**

There is a set `s` of four positive integers such that for any two distinct
elements `a, b ∈ s`, the number `a * b + 1` has a nontrivial square factor:
some `q > 1` satisfies `q * q ∣ a * b + 1`.

The witness is the classical Diophantine quadruple `{1, 3, 8, 120}`.  The
proof is by explicit case analysis on the six unordered (twelve ordered)
distinct pairs, supplying the exact square root `q` in each case:
`(a, b, q)` = `(1,3,2)`, `(1,8,3)`, `(1,120,11)`, `(3,8,5)`, `(3,120,19)`,
`(8,120,31)` and the same with `a`, `b` exchanged. -/
theorem jsp000701 : ∃ (s : Finset ℕ), s.card = 4 ∧
    ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ q : ℕ, 1 < q ∧ q * q ∣ a * b + 1 := by
  refine ⟨{1, 3, 8, 120}, by decide, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact ⟨2, by decide, by decide⟩
        | exact ⟨3, by decide, by decide⟩
        | exact ⟨5, by decide, by decide⟩
        | exact ⟨11, by decide, by decide⟩
        | exact ⟨19, by decide, by decide⟩
        | exact ⟨31, by decide, by decide⟩

#print axioms jsp000701
