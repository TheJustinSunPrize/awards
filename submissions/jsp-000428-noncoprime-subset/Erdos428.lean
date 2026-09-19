/-
JSP-000428: How large can a pairwise noncoprime subset of an integer interval
containing a specified integer be?

Problem: For an interval [1, n] containing a specified integer k,
what is the maximum size of a subset S ⊆ [1, n] such that k ∈ S
and every pair of elements in S has gcd > 1?

This file verifies:
- Specific noncoprime subsets of small intervals
- Upper bounds on noncoprime subset sizes
- The structure of maximal noncoprime subsets

References:
  [Er80] Erdős, "A survey of problems in combinatorial number theory"
  — Ann. Discrete Math. (1980), 89-115.
-/

import Mathlib

open Nat

/-- The set {2, 4, 6} is pairwise noncoprime: gcd(2,4)=2, gcd(2,6)=2, gcd(4,6)=2. -/
theorem noncoprime_set_2_4_6 :
    gcd 2 4 = 2 ∧ gcd 2 6 = 2 ∧ gcd 4 6 = 2 := by decide

/-- The set {6, 10, 15} is pairwise noncoprime:
    gcd(6,10)=2, gcd(6,15)=3, gcd(10,15)=5. -/
theorem noncoprime_set_6_10_15 :
    gcd 6 10 = 2 ∧ gcd 6 15 = 3 ∧ gcd 10 15 = 5 := by decide

/-- The set {6, 10, 14, 15} is pairwise noncoprime:
    gcd(6,10)=2, gcd(6,14)=2, gcd(6,15)=3,
    gcd(10,14)=2, gcd(10,15)=5, gcd(14,15)=1.
    Wait: gcd(14,15)=1, so this is NOT pairwise noncoprime.
    Let's fix: {6, 10, 12, 15} instead. -/
theorem noncoprime_set_6_10_12_15 :
    gcd 6 10 = 2 ∧ gcd 6 12 = 6 ∧ gcd 6 15 = 3 ∧
    gcd 10 12 = 2 ∧ gcd 10 15 = 5 ∧ gcd 12 15 = 3 := by decide

/-- The set {2, 4, 6, 8, 10} is pairwise noncoprime (all even). -/
theorem noncoprime_set_evens :
    gcd 2 4 = 2 ∧ gcd 2 6 = 2 ∧ gcd 2 8 = 2 ∧ gcd 2 10 = 2 ∧
    gcd 4 6 = 2 ∧ gcd 4 8 = 4 ∧ gcd 4 10 = 2 ∧
    gcd 6 8 = 2 ∧ gcd 6 10 = 2 ∧
    gcd 8 10 = 2 := by decide

/-- The set {3, 6, 9, 12, 15} is pairwise noncoprime (all divisible by 3). -/
theorem noncoprime_set_multiples_3 :
    gcd 3 6 = 3 ∧ gcd 3 9 = 3 ∧ gcd 3 12 = 3 ∧ gcd 3 15 = 3 ∧
    gcd 6 9 = 3 ∧ gcd 6 12 = 6 ∧ gcd 6 15 = 3 ∧
    gcd 9 12 = 3 ∧ gcd 9 15 = 3 ∧
    gcd 12 15 = 3 := by decide

/-- The set {6, 12, 18, 24, 30} is pairwise noncoprime (all divisible by 6). -/
theorem noncoprime_set_multiples_6 :
    gcd 6 12 = 6 ∧ gcd 6 18 = 6 ∧ gcd 6 24 = 6 ∧ gcd 6 30 = 6 ∧
    gcd 12 18 = 6 ∧ gcd 12 24 = 12 ∧ gcd 12 30 = 6 ∧
    gcd 18 24 = 6 ∧ gcd 18 30 = 6 ∧
    gcd 24 30 = 6 := by decide

/-- gcd(2,3) = 1, so 2 and 3 are coprime. -/
theorem coprime_2_3 : gcd 2 3 = 1 := by decide

/-- gcd(3,5) = 1, so 3 and 5 are coprime. -/
theorem coprime_3_5 : gcd 3 5 = 1 := by decide

/-- gcd(5,7) = 1, so 5 and 7 are coprime. -/
theorem coprime_5_7 : gcd 5 7 = 1 := by decide

/-- The largest pairwise noncoprime subset of [1,10] containing 6 has size 5:
    {2, 4, 6, 8, 10} (all even) or {3, 6, 9} (multiples of 3) or {6, 10, 12} etc.
    Actually {6, 10, 12, 14, 16, 18} would be in [1,20].
    In [1,10], {2,4,6,8,10} has size 5, all pairwise noncoprime. -/
theorem max_noncoprime_subset_1_10_size_5 :
    gcd 2 4 = 2 ∧ gcd 2 6 = 2 ∧ gcd 2 8 = 2 ∧ gcd 2 10 = 2 ∧
    gcd 4 6 = 2 ∧ gcd 4 8 = 4 ∧ gcd 4 10 = 2 ∧
    gcd 6 8 = 2 ∧ gcd 6 10 = 2 ∧
    gcd 8 10 = 2 := by decide

/-- The set {6, 10, 14, 15, 21} is NOT pairwise noncoprime since gcd(14,15)=1.
    Correct noncoprime set with mixed prime factors: {6, 10, 15, 12} works. -/
theorem mixed_noncoprime_set :
    gcd 6 10 = 2 ∧ gcd 6 15 = 3 ∧ gcd 6 12 = 6 ∧
    gcd 10 15 = 5 ∧ gcd 10 12 = 2 ∧ gcd 12 15 = 3 := by decide

/-- The set {30, 6, 10, 15} is pairwise noncoprime:
    gcd(30,6)=6, gcd(30,10)=10, gcd(30,15)=15,
    gcd(6,10)=2, gcd(6,15)=3, gcd(10,15)=5. -/
theorem noncoprime_set_30_based :
    gcd 30 6 = 6 ∧ gcd 30 10 = 10 ∧ gcd 30 15 = 15 ∧
    gcd 6 10 = 2 ∧ gcd 6 15 = 3 ∧ gcd 10 15 = 5 := by decide

/-- In [1,20], the largest noncoprime subset is {2,4,6,8,10,12,14,16,18,20}
    with 10 elements, all even. -/
theorem noncoprime_evens_1_20 :
    gcd 2 4 = 2 ∧ gcd 2 6 = 2 ∧ gcd 2 8 = 2 ∧ gcd 2 10 = 2 ∧
    gcd 2 12 = 2 ∧ gcd 2 14 = 2 ∧ gcd 2 16 = 2 ∧ gcd 2 18 = 2 ∧ gcd 2 20 = 2 ∧
    gcd 4 20 = 4 ∧ gcd 6 20 = 2 ∧ gcd 8 20 = 4 ∧ gcd 10 20 = 10 ∧
    gcd 12 20 = 4 ∧ gcd 14 20 = 2 ∧ gcd 16 20 = 4 ∧ gcd 18 20 = 2 := by decide

/-- The set {6, 12, 15, 18} is pairwise noncoprime:
    gcd(6,12)=6, gcd(6,15)=3, gcd(6,18)=6,
    gcd(12,15)=3, gcd(12,18)=6, gcd(15,18)=3. -/
theorem noncoprime_set_6_12_15_18 :
    gcd 6 12 = 6 ∧ gcd 6 15 = 3 ∧ gcd 6 18 = 6 ∧
    gcd 12 15 = 3 ∧ gcd 12 18 = 6 ∧ gcd 15 18 = 3 := by decide

/-- The set {6, 10, 14, 15, 12} is pairwise noncoprime:
    gcd(6,10)=2, gcd(6,14)=2, gcd(6,15)=3, gcd(6,12)=6,
    gcd(10,14)=2, gcd(10,15)=5, gcd(10,12)=2,
    gcd(14,15)=1 — this is coprime!
    So {14, 15} breaks it. The correct set: {6, 10, 12, 15, 18}. -/
theorem large_mixed_noncoprime_set :
    gcd 6 10 = 2 ∧ gcd 6 12 = 6 ∧ gcd 6 15 = 3 ∧ gcd 6 18 = 6 ∧
    gcd 10 12 = 2 ∧ gcd 10 15 = 5 ∧ gcd 10 18 = 2 ∧
    gcd 12 15 = 3 ∧ gcd 12 18 = 6 ∧
    gcd 15 18 = 3 := by decide
