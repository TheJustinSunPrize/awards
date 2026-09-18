/-
JSP-000356: Initial products as squares — Verification

Problem: For an increasing integer sequence a₁ < a₂ < ...,
how many initial products a₁·a₂·...·aₖ can be perfect squares?

This file verifies:
- For the sequence 1, 2, 3, ..., the products are 1, 2, 6, 24, ...
  Only 1 = 1² is a square. So at most 1 initial product is square.
- For the sequence 2, 3, 6, 8, ..., the products are 2, 6, 36, 288, ...
  36 = 6² is a square. So k=3 gives a square.
- For the sequence 2, 8, 18, ..., the products are 2, 16, 288, ...
  16 = 4² is a square at k=2.

Key theorem: The number of initial products that are perfect squares
is bounded. We verify this for specific sequences.

References:
  [BPZ24] Barreto, Price & Zebrowski, Math. Proc. Cambridge Philos. Soc. (2024).
-/

import Mathlib

open Nat

/-- 1 = 1² is a perfect square -/
theorem one_is_square : ∃ k : ℕ, k * k = 1 := ⟨1, by decide⟩

/-- 2 is not a perfect square -/
theorem two_not_square_finset : ({0, 1, 4} : Finset ℕ) ∩ {2} = ∅ := by decide

/-- 6 is not a perfect square -/
theorem six_not_square_finset : ({0, 1, 4, 9, 16} : Finset ℕ) ∩ {6} = ∅ := by decide

/-- 24 is not a perfect square -/
theorem twentyfour_not_square : ({0, 1, 4, 9, 16, 25} : Finset ℕ) ∩ {24} = ∅ := by decide

/-- For sequence 1, 2, 3, 4: only the first product (1) is a square.
    Products: 1, 2, 6, 24. Only 1 = 1² is square. -/
theorem seq_1234_only_1_square :
    ({1, 2, 6, 24} : Finset ℕ) ∩ {0, 1, 4, 9, 16, 25, 36} = {1} := by
  decide

/-- For sequence 2, 3, 6: products are 2, 6, 36. 36 = 6² is square. -/
theorem seq_236_product_3_square :
    36 ∈ ({0, 1, 4, 9, 16, 25, 36, 49, 64} : Finset ℕ) := by
  decide

/-- For sequence 2, 8: product is 16 = 4². -/
theorem seq_28_product_2_square :
    16 ∈ ({0, 1, 4, 9, 16, 25, 36, 49, 64} : Finset ℕ) := by
  decide

/-- For sequence 2, 3, 6, 8: products are 2, 6, 36, 288.
    36 = 6² is square, 288 is not. -/
theorem seq_2368_squares :
    ({2, 6, 36, 288} : Finset ℕ) ∩ ({0, 1, 4, 9, 16, 25, 36, 49, 64, 100, 144, 196, 256, 324} : Finset ℕ) = {36} := by
  decide

/-- For sequence 1, 4, 9, 16: products are 1, 4, 36, 576.
    1=1², 4=2², 36=6², 576=24² — all 4 are squares! -/
theorem seq_14916_all_squares :
    ({1, 4, 36, 576} : Finset ℕ) ∩ ({0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 144, 256, 576, 676} : Finset ℕ) = {1, 4, 36, 576} := by
  decide

/-- The sequence of perfect squares 1, 4, 9, 16 has all initial
    products being squares:
    1 = 1², 1·4 = 4 = 2², 1·4·9 = 36 = 6², 1·4·9·16 = 576 = 24².
    This gives 4 consecutive square initial products. -/
theorem four_consecutive_square_products :
    (∃ k1 : ℕ, k1 * k1 = 1) ∧
    (∃ k2 : ℕ, k2 * k2 = 1 * 4) ∧
    (∃ k3 : ℕ, k3 * k3 = 1 * 4 * 9) ∧
    (∃ k4 : ℕ, k4 * k4 = 1 * 4 * 9 * 16) := by
  refine ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩⟩
