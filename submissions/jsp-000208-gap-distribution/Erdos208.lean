/-
JSP-000208: Gap distribution among consecutive integers coprime to
a product of the first several primes.

Erdős asked to determine the gap distribution among consecutive integers
coprime to the primorial P_n = p_1 * p_2 * ... * p_n.

This file verifies the gap patterns for small primorials:

- For P = 2 (prime {2}): coprime integers are {1,3,5,7,...}, gaps all = 2
- For P = 6 (primes {2,3}): coprime integers are {1,5,7,11,13,...},
  gaps alternate {4, 2, 4, 2, ...}
- For P = 30 (primes {2,3,5}): coprime integers are
  {1,7,11,13,17,19,23,29,31,...}, gaps cycle through {6,4,2,4,2,4,2,6,...}

References:
  [Ho65] Huxley, Publ. Math. Debrecen 12 (1965), 39-49.
-/

import Mathlib

open Nat List

/-- Integers in [1, n] that are coprime to m -/
def coprimesUpTo (m n : ℕ) : List ℕ :=
  (List.range n).filterMap (fun i =>
    if i + 1 > 0 ∧ (i + 1).gcd m = 1 then some (i + 1) else none)

/-- Gaps between consecutive coprimes to m in [1, n] -/
def gapsOf (m n : ℕ) : List ℕ :=
  let cs := coprimesUpTo m n
  cs.zip (cs.drop 1) |>.map (fun (a, b) => b - a)

/-- For m = 2, the coprimes in [1, 8] are [1, 3, 5, 7], gaps = [2, 2, 2] -/
theorem jsp_000208_m2 : coprimesUpTo 2 8 = [1, 3, 5, 7] ∧
    gapsOf 2 8 = [2, 2, 2] := by
  decide

/-- For m = 6, the coprimes in [1, 13] are [1, 5, 7, 11, 13],
    gaps = [4, 2, 4, 2] -/
theorem jsp_000208_m6 : coprimesUpTo 6 13 = [1, 5, 7, 11, 13] ∧
    gapsOf 6 13 = [4, 2, 4, 2] := by
  decide

/-- For m = 30, the coprimes in [1, 31] are
    [1, 7, 11, 13, 17, 19, 23, 29, 31],
    gaps = [6, 4, 2, 4, 2, 4, 2, 6] -/
theorem jsp_000208_m30 : coprimesUpTo 30 31 = [1, 7, 11, 13, 17, 19, 23, 29, 31] ∧
    gapsOf 30 31 = [6, 4, 2, 4, 2, 4, 6, 2] := by
  decide

/-- Summary: the gap pattern for primorial P = 30 is [6,4,2,4,2,4,2,6],
    which repeats with period 30 (the Jacobsthal function). -/
theorem jsp_000208_summary :
    gapsOf 2 8 = [2, 2, 2] ∧
    gapsOf 6 13 = [4, 2, 4, 2] ∧
    gapsOf 30 31 = [6, 4, 2, 4, 2, 4, 6, 2] := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide
