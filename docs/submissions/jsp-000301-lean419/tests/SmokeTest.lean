import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

example : (23 : Nat) ^ 3 = 12167 := by
  norm_num
