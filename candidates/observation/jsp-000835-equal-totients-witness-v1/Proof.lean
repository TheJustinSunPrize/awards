/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/

import Mathlib.Data.Nat.Totient

/-!
# JSP-000835 observation: an explicit witness of consecutive equal totients

The Justin Sun Prize problem
[JSP-000835](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000835)
asks: *Are there infinitely many consecutive positive integers with equal
totients?*  This file records a complete, machine-checked Lean proof of an
explicit instance of consecutive positive integers with equal Euler totients:

* `φ(15) = φ(16) = 8`

Here `φ` is Mathlib's `Nat.totient`, the Euler totient function.

**Scope.**  The infinitude question asked by the catalog entry is *not*
addressed, the catalogued problem is not resolved, and no award claim is made.
-/

/-- The consecutive positive integers `15` and `16` have equal Euler totients:
`φ(15) = φ(16) = 8`. -/
theorem consecutive_equal_totients : Nat.totient 15 = Nat.totient 16 := by
  decide

/-- The common totient value of the witness pair is `8`: `φ(15) = 8`. -/
theorem totient_fifteen_eq_eight : Nat.totient 15 = 8 := by
  decide

/-- The common totient value of the witness pair is `8`: `φ(16) = 8`. -/
theorem totient_sixteen_eq_eight : Nat.totient 16 = 8 := by
  decide

/-- Combined form of the witness: `φ(15) = 8 ∧ φ(16) = 8`. -/
theorem consecutive_equal_totients_values :
    Nat.totient 15 = 8 ∧ Nat.totient 16 = 8 := by
  decide
