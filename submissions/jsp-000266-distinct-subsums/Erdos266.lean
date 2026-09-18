/-
JSP-000266: How many distinct subset sums do the reciprocals of the
first several positive integers have?

Erdős asked about the number of distinct values of Σ_{i∈S} 1/i
where S ⊆ {1, ..., n}. Bleicher and Erdős (1975) proved a lower bound.

This file formalizes the exact count for small n by working with
integers (scaled by the LCM of denominators) to avoid rational arithmetic.

For n = 3, the LCM of {1, 2, 3} is 6, so we work with {6, 3, 2}
and verify that all 2^3 = 8 subset sums are distinct.

References:
  [BlEr75] Bleicher and Erdős, Math. Comp. 29 (1975), 29-42.
-/

import Mathlib

open Finset

/-- Subset sums of {6, 3, 2} (scaled reciprocals of {1, 1/2, 1/3}).
    We use a List to avoid Finset.range indexing issues. -/
def scaledSums3 : Finset ℕ :=
  (Finset.range 3).powerset.image (fun s =>
    s.sum (fun i => [6, 3, 2][i]!))

/-- Subset sums of {2, 1} (scaled reciprocals of {1, 1/2}, LCM = 2). -/
def scaledSums2 : Finset ℕ :=
  (Finset.range 2).powerset.image (fun s =>
    s.sum (fun i => [2, 1][i]!))

/-- Subset sums of {1} (scaled reciprocals of {1}). -/
def scaledSums1 : Finset ℕ :=
  (Finset.range 1).powerset.image (fun s =>
    s.sum (fun i => [1][i]!))

/-- For n = 1, the subset sums of {1} are {0, 1}, giving 2 distinct values. -/
theorem jsp_000266_n1 : scaledSums1.card = 2 := by
  decide

/-- For n = 2, all 4 subset sums of {2, 1} are distinct. -/
theorem jsp_000266_n2 : scaledSums2.card = 4 := by
  decide

/-- For n = 3, all 8 subset sums of {6, 3, 2} are distinct.
    This means all 2^3 subset sums of {1, 1/2, 1/3} are distinct. -/
theorem jsp_000266_n3 : scaledSums3.card = 8 := by
  decide

/-- Summary: for n = 1, 2, 3, the number of distinct subset sums
    of {1, 1/2, ..., 1/n} equals 2^n. All 2^n subsets give distinct
    sums, verified computationally via integer scaling. -/
theorem jsp_000266_exact_count :
    scaledSums1.card = 2 ∧ scaledSums2.card = 4 ∧ scaledSums3.card = 8 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide
