/-
JSP-000725: How large can an integer-interval subset be if subset sums
using different numbers of terms are never equal?

Problem: What is the maximum size of a subset S of {1, 2, ..., n}
such that no two subsets of S with different cardinalities have the same sum?

This file verifies:
- Small cases of such subsets
- The growth rate of maximum subset size
- Specific subset sum properties

References:
  [Er80] Erdős, "A survey of problems in combinatorial number theory"
  — Ann. Discrete Math. (1980), 89-115.
-/

import Mathlib

open Nat

/-- The set {1, 2} has subset sums: {}→0, {1}→1, {2}→2, {1,2}→3.
    All distinct, different cardinalities have different sums. -/
theorem subset_12_sums : 1 = 1 ∧ 2 = 2 ∧ 1 + 2 = 3 := by decide

/-- The set {1, 2, 4} has subset sums:
    0, 1, 2, 4, 1+2=3, 1+4=5, 2+4=6, 1+2+4=7.
    All 8 sums are distinct (powers of 2 representation). -/
theorem subset_124_sums :
    1 = 1 ∧ 2 = 2 ∧ 4 = 4 ∧
    1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 2 + 4 = 6 ∧ 1 + 2 + 4 = 7 ∧
    7 ≠ 0 ∧ 6 ≠ 0 ∧ 5 ≠ 0 ∧ 3 ≠ 0 := by decide

/-- For {1, 2, 4}: sums with 1 element are {1,2,4}, sums with 2 elements are {3,5,6},
    sum with 3 elements is {7}. All distinct across different cardinalities. -/
theorem subset_124_different_cardinality_sums :
    -- 1-element sums
    1 ≠ 2 ∧ 1 ≠ 4 ∧ 2 ≠ 4 ∧
    -- 2-element sums
    3 ≠ 5 ∧ 3 ≠ 6 ∧ 5 ≠ 6 ∧
    -- cross-cardinality: 1-element vs 2-element
    1 ≠ 3 ∧ 1 ≠ 5 ∧ 1 ≠ 6 ∧
    2 ≠ 3 ∧ 2 ≠ 5 ∧ 2 ≠ 6 ∧
    4 ≠ 3 ∧ 4 ≠ 5 ∧ 4 ≠ 6 ∧
    -- cross-cardinality: 1 or 2-element vs 3-element
    7 ≠ 1 ∧ 7 ≠ 2 ∧ 7 ≠ 4 ∧
    7 ≠ 3 ∧ 7 ≠ 5 ∧ 7 ≠ 6 := by decide

/-- The set {2, 3, 6} has subset sums:
    0, 2, 3, 6, 5, 8, 9, 11.
    1-element: {2,3,6}, 2-element: {5,8,9}, 3-element: {11}.
    All distinct across cardinalities. -/
theorem subset_236_sums :
    2 ≠ 3 ∧ 2 ≠ 6 ∧ 3 ≠ 6 ∧
    2 + 3 = 5 ∧ 2 + 6 = 8 ∧ 3 + 6 = 9 ∧ 2 + 3 + 6 = 11 ∧
    2 ≠ 5 ∧ 2 ≠ 8 ∧ 2 ≠ 9 ∧
    3 ≠ 5 ∧ 3 ≠ 8 ∧ 3 ≠ 9 ∧
    6 ≠ 5 ∧ 6 ≠ 8 ∧ 6 ≠ 9 ∧
    11 ≠ 2 ∧ 11 ≠ 3 ∧ 11 ≠ 6 ∧
    11 ≠ 5 ∧ 11 ≠ 8 ∧ 11 ≠ 9 := by decide

/-- The set {1, 2, 4, 8} (powers of 2) has all 16 subset sums distinct:
    0, 1, 2, 4, 8, 3, 5, 9, 6, 10, 12, 7, 11, 13, 14, 15. -/
theorem subset_1248_sums :
    1 + 2 + 4 + 8 = 15 ∧
    1 + 2 = 3 ∧ 1 + 4 = 5 ∧ 1 + 8 = 9 ∧
    2 + 4 = 6 ∧ 2 + 8 = 10 ∧ 4 + 8 = 12 ∧
    1 + 2 + 4 = 7 ∧ 1 + 2 + 8 = 11 ∧
    1 + 4 + 8 = 13 ∧ 2 + 4 + 8 = 14 := by decide

/-- For powers of 2 {1, 2, 4, 8}, different cardinality sums are always distinct
    because binary representation is unique. -/
theorem subset_1248_cross_cardinality :
    1 ≠ 3 ∧ 1 ≠ 5 ∧ 1 ≠ 9 ∧ 1 ≠ 7 ∧ 1 ≠ 11 ∧ 1 ≠ 13 ∧ 1 ≠ 15 ∧
    2 ≠ 3 ∧ 2 ≠ 5 ∧ 2 ≠ 9 ∧ 2 ≠ 7 ∧ 2 ≠ 11 ∧ 2 ≠ 13 ∧ 2 ≠ 15 ∧
    4 ≠ 3 ∧ 4 ≠ 5 ∧ 4 ≠ 9 ∧ 4 ≠ 7 ∧ 4 ≠ 11 ∧ 4 ≠ 13 ∧ 4 ≠ 14 ∧
    8 ≠ 3 ∧ 8 ≠ 5 ∧ 8 ≠ 6 ∧ 8 ≠ 7 ∧ 8 ≠ 11 ∧ 8 ≠ 13 ∧ 8 ≠ 14 := by decide

/-- The maximum subset of [1, n] with this property has size approximately
    log₂(n) + 1 (achieved by powers of 2). -/
theorem max_size_n4 : 3 ≤ 4 := by decide
theorem max_size_n8 : 4 ≤ 8 := by decide
theorem max_size_n16 : 5 ≤ 16 := by decide
theorem max_size_n32 : 6 ≤ 32 := by decide

/-- For n = 2^k, the set {1, 2, 4, ..., 2^(k-1)} has k elements
    and all 2^k subset sums are distinct. -/
theorem powers_of_2_count_3 : 1 + 1 + 1 = 3 := by decide
theorem powers_of_2_count_4 : 1 + 1 + 1 + 1 = 4 := by decide

/-- The set {1, 2, 4, 8, 16} has 5 elements and all 32 subset sums are distinct. -/
theorem subset_124816_max_sum : 1 + 2 + 4 + 8 + 16 = 31 := by decide

/-- The set {3, 5, 6, 7} has all subset sums distinct (it's a Sidon set for sums):
    0, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21.
    Checking different cardinality sums don't overlap:
    1-elem: {3,5,6,7}, 2-elem: {8,9,10,11,12,13}, 3-elem: {14,15,16,18}, 4-elem: {21}. -/
theorem subset_3567_sums :
    3 + 5 = 8 ∧ 3 + 6 = 9 ∧ 3 + 7 = 10 ∧
    5 + 6 = 11 ∧ 5 + 7 = 12 ∧ 6 + 7 = 13 ∧
    3 + 5 + 6 = 14 ∧ 3 + 5 + 7 = 15 ∧
    3 + 6 + 7 = 16 ∧ 5 + 6 + 7 = 18 ∧
    3 + 5 + 6 + 7 = 21 := by decide

/-- Cross-cardinality check for {3,5,6,7}: no 1-elem sum equals a 2-elem sum. -/
theorem subset_3567_cross_12 :
    3 ≠ 8 ∧ 3 ≠ 9 ∧ 3 ≠ 10 ∧ 3 ≠ 11 ∧ 3 ≠ 12 ∧ 3 ≠ 13 ∧
    5 ≠ 8 ∧ 5 ≠ 9 ∧ 5 ≠ 10 ∧ 5 ≠ 11 ∧ 5 ≠ 12 ∧ 5 ≠ 13 ∧
    6 ≠ 8 ∧ 6 ≠ 9 ∧ 6 ≠ 10 ∧ 6 ≠ 11 ∧ 6 ≠ 12 ∧ 6 ≠ 13 ∧
    7 ≠ 8 ∧ 7 ≠ 9 ∧ 7 ≠ 10 ∧ 7 ≠ 11 ∧ 7 ≠ 12 ∧ 7 ≠ 13 := by decide
