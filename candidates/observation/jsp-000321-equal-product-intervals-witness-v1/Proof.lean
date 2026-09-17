/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/

import Mathlib

/-!
# JSP-000321: an equal-product witness of two disjoint intervals of consecutive positive integers

The catalogued problem JSP-000321 asks: *"When can two disjoint intervals of
consecutive positive integers have equal products?"*
(https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000321)

This file records one explicit instance of the phenomenon: the disjoint
intervals `[5, 7]` and `[14, 15]` of consecutive positive integers have equal
products, since `5 * 6 * 7 = 210 = 14 * 15`, and they are disjoint because
`7 < 14`.

## Scope

This observation records one explicit instance only.  The classification of
*all* such instances requested by the question is not addressed, the
catalogued problem JSP-000321 is not resolved, and no award claim is made.

## Attribution

Formalization author: Yaohua-Leo, AI-assisted via ZCode (GLM).
-/

/-- **An equal-product witness for JSP-000321.**  The intervals `[5, 7]` and
`[14, 15]` of consecutive positive integers are disjoint (`7 < 14`) and have
equal products: `5 * 6 * 7 = 210 = 14 * 15`. -/
theorem equal_product_intervals :
    (5 : ℕ) * 6 * 7 = (14 : ℕ) * 15 ∧ (7 : ℕ) < 14 := by
  decide
