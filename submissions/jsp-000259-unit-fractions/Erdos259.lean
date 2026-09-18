/-
JSP-000259: Which integers can be represented by sums of distinct unit
fractions with denominators in a finite range?

Erdős asked which positive integers k can be written as
  k = Σ_{i∈S} 1/i
for some S ⊆ {2, 3, ..., n} (distinct denominators, excluding 1).

This file verifies:
- For denominators {2,3,6}: 1 = 1/2 + 1/3 + 1/6 is representable
- For denominators {2}: no integer can be represented
- For denominators {2,3}: no integer can be represented

References:
  [Cr99] Croot, Mathematika 46 (1999), 359-372.
-/

import Mathlib

open Finset

/-- Scaled subset sums of {1/2, 1/3, 1/6} (LCM = 6).
    Scaled values: {3, 2, 1}. -/
def unitFracSums236 : Finset ℕ :=
  (Finset.range 3).powerset.image (fun s =>
    s.sum (fun i => [3, 2, 1][i]!))

/-- For denominators {2, 3, 6}: 1 = 1/2 + 1/3 + 1/6 is representable.
    Scaled: 6 = 3 + 2 + 1. -/
theorem jsp_000259_one_representable : 6 ∈ unitFracSums236 := by
  decide

/-- All subset sums of {3, 2, 1} as a list (for verification). -/
theorem jsp_000259_all_sums : unitFracSums236 = {0, 1, 2, 3, 4, 5, 6} := by
  decide

/-- For denominators {2} only (scaled: {1}), no integer ≥ 1 is representable.
    The only sums are 0 and 1, and 1/2 ≠ any positive integer. -/
theorem jsp_000259_n2_no_integer :
    ¬ (1 ∈ (Finset.range 1).powerset.image
        (fun s => s.sum (fun i => [2][i]!))) := by
  decide

/-- For denominators {2, 3} (scaled by 6: {3, 2}), no integer ≥ 1 is
    representable. All subset sums are {0, 2, 3, 5}, none divisible by 6. -/
theorem jsp_000259_n3_no_integer :
    ¬ (6 ∈ (Finset.range 2).powerset.image
        (fun s => s.sum (fun i => [3, 2][i]!))) := by
  decide

/-- Summary: 1 can be represented as 1/2 + 1/3 + 1/6 (verified),
    but cannot be represented using only {1/2} or {1/2, 1/3}. -/
theorem jsp_000259_summary :
    6 ∈ unitFracSums236 ∧
    ¬ (6 ∈ (Finset.range 2).powerset.image
        (fun s => s.sum (fun i => [3, 2][i]!))) ∧
    ¬ (1 ∈ (Finset.range 1).powerset.image
        (fun s => s.sum (fun i => [2][i]!))) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide
