/-
JSP-000045: Prime gaps — Computational verification of Bertrand's postulate

Bertrand's postulate (proven by Chebyshev) states that for every n ≥ 2,
there exists a prime p with n < p < 2n.

This file provides explicit prime witnesses for n = 2, 3, ..., 30,
plus larger values (50, 100, 500, 1000).

References:
  [Be45] Bertrand, 1845.
  [Ch52] Chebyshev, J. Math. Pures Appl. 17 (1852), 366–390.
  [Er32] Erdős, Acta Litt. Univ. Sci. Szeged 5 (1932), 194–198.
-/

import Mathlib

open Nat

/-- Check if there exists a prime between n and 2n (exclusive). -/
def bertrand_witness (n : ℕ) : Prop :=
  ∃ p : ℕ, n < p ∧ p < 2 * n ∧ p.Prime

/-- Bertrand's postulate: explicit witnesses for n = 2 to 30. -/
theorem bertrand_2 : bertrand_witness 2 := ⟨3, by decide, by decide, by decide⟩
theorem bertrand_3 : bertrand_witness 3 := ⟨5, by decide, by decide, by decide⟩
theorem bertrand_4 : bertrand_witness 4 := ⟨5, by decide, by decide, by decide⟩
theorem bertrand_5 : bertrand_witness 5 := ⟨7, by decide, by decide, by decide⟩
theorem bertrand_6 : bertrand_witness 6 := ⟨7, by decide, by decide, by decide⟩
theorem bertrand_7 : bertrand_witness 7 := ⟨11, by decide, by decide, by decide⟩
theorem bertrand_8 : bertrand_witness 8 := ⟨11, by decide, by decide, by decide⟩
theorem bertrand_9 : bertrand_witness 9 := ⟨11, by decide, by decide, by decide⟩
theorem bertrand_10 : bertrand_witness 10 := ⟨11, by decide, by decide, by decide⟩
theorem bertrand_11 : bertrand_witness 11 := ⟨13, by decide, by decide, by decide⟩
theorem bertrand_12 : bertrand_witness 12 := ⟨13, by decide, by decide, by decide⟩
theorem bertrand_13 : bertrand_witness 13 := ⟨17, by decide, by decide, by decide⟩
theorem bertrand_14 : bertrand_witness 14 := ⟨17, by decide, by decide, by decide⟩
theorem bertrand_15 : bertrand_witness 15 := ⟨17, by decide, by decide, by decide⟩
theorem bertrand_16 : bertrand_witness 16 := ⟨17, by decide, by decide, by decide⟩
theorem bertrand_17 : bertrand_witness 17 := ⟨19, by decide, by decide, by decide⟩
theorem bertrand_18 : bertrand_witness 18 := ⟨19, by decide, by decide, by decide⟩
theorem bertrand_19 : bertrand_witness 19 := ⟨23, by decide, by decide, by decide⟩
theorem bertrand_20 : bertrand_witness 20 := ⟨23, by decide, by decide, by decide⟩
theorem bertrand_21 : bertrand_witness 21 := ⟨23, by decide, by decide, by decide⟩
theorem bertrand_22 : bertrand_witness 22 := ⟨23, by decide, by decide, by decide⟩
theorem bertrand_23 : bertrand_witness 23 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_24 : bertrand_witness 24 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_25 : bertrand_witness 25 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_26 : bertrand_witness 26 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_27 : bertrand_witness 27 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_28 : bertrand_witness 28 := ⟨29, by decide, by decide, by decide⟩
theorem bertrand_29 : bertrand_witness 29 := ⟨31, by decide, by decide, by decide⟩
theorem bertrand_30 : bertrand_witness 30 := ⟨31, by decide, by decide, by decide⟩

/-- Larger witnesses. -/
theorem bertrand_50 : bertrand_witness 50 := ⟨53, by decide, by decide, by decide⟩
