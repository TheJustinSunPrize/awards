import Std

namespace EgyptianLargestDenominator

/-- A representation of a positive rational number as a sum of distinct unit fractions.
    We represent the collection of denominators as a strictly increasing list of natural numbers >= 2. -/

def StrictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (x < y) && StrictlyIncreasing (y :: rest)

def ValidDenominators (xs : List Nat) : Bool :=
  StrictlyIncreasing xs && xs.all (fun x => 2 ≤ x)

/-- Sum of reciprocals with a common denominator.
    For a list of positive integers `xs` and a common multiple `M`,
    the sum is sum_{x in xs} (M / x).
    If M is divisible by each x in xs, sum of 1/x = 1 iff sum_{x in xs} (M / x) = M. -/

def common_sum (M : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + M / x) 0

/-- Exact witness that sum_{x in xs} (1/x) = 1 via common multiple M -/
def IsUnitFractionPartitionOfOne (xs : List Nat) (M : Nat) : Bool :=
  ValidDenominators xs &&
  xs.all (fun x => x > 0 && M % x == 0) &&
  (common_sum M xs == M)

/-- Theorem: [2, 3, 6] is a valid unit fraction representation of 1 with largest denominator 6 -/
theorem witness_six : IsUnitFractionPartitionOfOne [2, 3, 6] 6 = true := by
  decide

/-- Theorem: [2, 4, 6, 12] is a valid unit fraction representation of 1 with largest denominator 12 -/
theorem witness_twelve : IsUnitFractionPartitionOfOne [2, 4, 6, 12] 12 = true := by
  decide

/-- Theorem: [2, 3, 9, 18] is a valid unit fraction representation of 1 with largest denominator 18 -/
theorem witness_eighteen : IsUnitFractionPartitionOfOne [2, 3, 9, 18] 18 = true := by
  decide

/-- Theorem: [2, 4, 5, 20] is a valid unit fraction representation of 1 with largest denominator 20 -/
theorem witness_twenty : IsUnitFractionPartitionOfOne [2, 4, 5, 20] 20 = true := by
  decide

/-- Theorem: [2, 3, 8, 24] is a valid unit fraction representation of 1 with largest denominator 24 -/
theorem witness_twenty_four : IsUnitFractionPartitionOfOne [2, 3, 8, 24] 24 = true := by
  decide

/-- Exhaustive finite check: no sublist of [2, 3, 4, 5] has unit fraction sum equal to 1.
    We check this over the common multiple 60:
    for every nonempty sublist of [2, 3, 4, 5], sum_{x} (60 / x) != 60. -/
def no_sublist_sums_to_one (M : Nat) : List (List Nat) → Bool
  | [] => true
  | s :: rest =>
    let s_val := common_sum M s
    if s_val == M then false else no_sublist_sums_to_one M rest

def sublists_2345 : List (List Nat) :=
  [ [2], [3], [4], [5],
    [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5],
    [2, 3, 4], [2, 3, 5], [2, 4, 5], [3, 4, 5],
    [2, 3, 4, 5] ]

/-- Theorem: No subset of {2, 3, 4, 5} sums to 1.
    Therefore, no integer N <= 5 can serve as the largest denominator in a representation of 1. -/
theorem bounded_five_impossible : no_sublist_sums_to_one 60 sublists_2345 = true := by
  decide

end EgyptianLargestDenominator
