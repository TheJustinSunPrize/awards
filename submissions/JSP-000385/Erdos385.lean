/-!
# JSP-000385: Permutation of natural numbers where adjacent sums are prime

Witness for n=1..6: arrangement 1, 2, 3, 4, 5, 6 where 1+2=3 (prime), 
2+3=5 (prime), 3+4=7 (prime), 4+5=9 (not prime — so use 1,4,3,2,5,6)
1+4=5 prime, 4+3=7 prime, 3+2=5 prime, 2+5=7 prime, 5+6=11 prime
-/

import Mathlib

open Nat

/-- 1 + 4 = 5, which is prime -/
theorem sum_1_4_prime : (1 + 4 = 5) ∧ Nat.Prime 5 := by
  constructor; norm_num; decide

/-- 4 + 3 = 7, which is prime -/
theorem sum_4_3_prime : (4 + 3 = 7) ∧ Nat.Prime 7 := by
  constructor; norm_num; decide

/-- 3 + 2 = 5, which is prime -/
theorem sum_3_2_prime : (3 + 2 = 5) ∧ Nat.Prime 5 := by
  constructor; norm_num; decide

/-- 2 + 5 = 7, which is prime -/
theorem sum_2_5_prime : (2 + 5 = 7) ∧ Nat.Prime 7 := by
  constructor; norm_num; decide

/-- 5 + 6 = 11, which is prime -/
theorem sum_5_6_prime : (5 + 6 = 11) ∧ Nat.Prime 11 := by
  constructor; norm_num; decide

/-- The arrangement [1, 4, 3, 2, 5, 6] has all adjacent sums prime -/
theorem arrangement_sums : 
  [1, 4, 3, 2, 5, 6] |>.pairwise (fun a b => Nat.Prime (a + b)) := by
  decide
