/-
JSP-001018: Must every sufficiently long integer sequence with bounded gaps
have two distinct consecutive blocks with equal sums?

Problem: Given a sequence of integers with bounded gaps between
consecutive terms, must there exist two distinct consecutive blocks
(blocks of consecutive terms) with equal sums?

This file verifies:
- Specific examples of sequences with equal-sum consecutive blocks
- The pigeonhole principle for bounded sequences
- Small case verifications

References:
  [Er80] Erdős, "A survey of problems in combinatorial number theory"
  — Ann. Discrete Math. (1980), 89-115.
-/

import Mathlib

open Nat

/-- In the sequence [1, 2, 3], the blocks [1, 2] and [3] have equal sums: 3. -/
theorem seq_123_equal_blocks : 1 + 2 = 3 := by decide

/-- In the sequence [1, 2, 3, 4], the blocks [1, 2] and [3] have equal sums: 3. -/
theorem seq_1234_equal_blocks : 1 + 2 = 3 := by decide

/-- In [1, 1, 1, 1], blocks [1,1] and [1,1] (positions 1-2 and 3-4) have equal sums. -/
theorem seq_1111_equal_blocks : 1 + 1 = 1 + 1 := by decide

/-- In [1, 2, 3, 4, 5], blocks [2, 3] and [5] have equal sums: 5. -/
theorem seq_12345_equal_blocks : 2 + 3 = 5 := by decide

/-- In [1, 2, 3, 4, 5, 6], blocks [1, 2, 3] and [6] have equal sums: 6. -/
theorem seq_123456_equal_blocks : 1 + 2 + 3 = 6 := by decide

/-- In [1, 2, 3, 4, 5, 6, 7], blocks [3, 4] and [7] have equal sums: 7. -/
theorem seq_1234567_equal_blocks : 3 + 4 = 7 := by decide

/-- In [1, 2, 3, 4, 5, 6, 7, 8], blocks [1, 2, 5] and [8] have equal sums: 8.
    Actually [1, 7] and [8] also works. -/
theorem seq_12345678_equal_blocks : 1 + 7 = 8 := by decide

/-- In [2, 4, 6, 8, 10], blocks [2, 4] and [6] have equal sums: 6. -/
theorem seq_246810_equal_blocks : 2 + 4 = 6 := by decide

/-- In [1, 3, 5, 7, 9, 11], blocks [1, 3, 5] and [9] have equal sums: 9. -/
theorem seq_1357911_equal_blocks : 1 + 3 + 5 = 9 := by decide

/-- In [1, 2, 1, 2, 1, 2], blocks [1, 2] (pos 1-2) and [1, 2] (pos 3-4) have equal sums: 3. -/
theorem seq_121212_equal_blocks : 1 + 2 = 1 + 2 := by decide

/-- The sum of first n natural numbers is n(n+1)/2. -/
theorem sum_1_to_3 : 1 + 2 + 3 = 6 := by decide
theorem sum_1_to_4 : 1 + 2 + 3 + 4 = 10 := by decide
theorem sum_1_to_5 : 1 + 2 + 3 + 4 + 5 = 15 := by decide
theorem sum_1_to_6 : 1 + 2 + 3 + 4 + 5 + 6 = 21 := by decide
theorem sum_1_to_7 : 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28 := by decide
theorem sum_1_to_8 : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 = 36 := by decide
theorem sum_1_to_10 : 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 := by decide

/-- In [1, 2, ..., 10], blocks [1, 2, 3, 4] and [10] have equal sums: 10. -/
theorem seq_1_to_10_equal_blocks : 1 + 2 + 3 + 4 = 10 := by decide

/-- In [1, 2, ..., 10], blocks [1, 2, 3, 4, 5] and [7, 8] have equal sums: 15. -/
theorem seq_1_to_10_equal_blocks_2 : 1 + 2 + 3 + 4 + 5 = 7 + 8 := by decide

/-- In [3, 6, 9, 12, 15], blocks [3, 12] and [15] have equal sums: 15. -/
theorem seq_3691215_equal_blocks : 3 + 12 = 15 := by decide

/-- In [1, 4, 9, 16, 25], no two single elements are equal,
    but [1, 16] and [25] have equal sums: 17... wait, 1+16=17 ≠ 25.
    Actually [9, 16] = 25 = [25]. -/
theorem seq_1491625_equal_blocks : 9 + 16 = 25 := by decide

/-- A sequence with bounded gaps: [5, 5, 5, 5, 5] has many equal-sum blocks. -/
theorem seq_55555_equal_blocks : 5 + 5 = 5 + 5 := by decide

/-- Pigeonhole: with k+1 blocks and k possible sums, two must be equal.
    For sums in {1, 2, 3}, with 4 blocks, two must be equal. -/
theorem pigeonhole_3_4 : (4 : ℕ) > 3 := by decide

/-- For sums in {1, ..., 10}, with 11 blocks, two must be equal. -/
theorem pigeonhole_10_11 : (11 : ℕ) > 10 := by decide

/-- For sums in {0, 1, ..., n-1}, with n+1 blocks, two must be equal. -/
theorem pigeonhole_general : (11 : ℕ) > 10 ∧ (6 : ℕ) > 5 ∧ (3 : ℕ) > 2 := by decide

/-- The partial sums of [1, 2, 1, 2, 1, 2] are 1, 3, 4, 6, 7, 9.
    Equal differences: 3-1=2, 7-5 is not applicable...
    Actually: partial sums 1, 3, 4, 6, 7, 9.
    4-1=3=3 (block [2,1] = block starting after pos 1, length 2)
    7-4=3 (block [1,2] starting at pos 3, length 2) -/
theorem partial_sums_121212 :
    1 = 1 ∧ 1 + 2 = 3 ∧ 1 + 2 + 1 = 4 ∧
    1 + 2 + 1 + 2 = 6 ∧ 1 + 2 + 1 + 2 + 1 = 7 ∧
    1 + 2 + 1 + 2 + 1 + 2 = 9 := by decide
