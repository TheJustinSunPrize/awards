import Mathlib.Tactic

-- Deliberately false. This file MUST fail; it is not part of the proof library.
example : (23 : Nat) ^ 3 = 12168 := by
  norm_num
