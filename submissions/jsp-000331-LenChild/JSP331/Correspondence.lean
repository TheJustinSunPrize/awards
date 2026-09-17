import JSP331.Statement
import Mathlib.Algebra.Order.Field.Basic

namespace JSP331

/-- For cardinality at least two, a positive-element gcd bound forces distinct witnesses. -/
theorem distinct_of_gcd_bound {A : Finset ℕ} (hzero : 0 ∉ A) (hcard : 2 ≤ A.card)
    {a b : ℕ} (ha : a ∈ A) (hbound : (a.gcd b : ℚ) ≤ (a : ℚ) / A.card) :
    a ≠ b := by
  intro hab
  subst b
  rw [Nat.gcd_self] at hbound
  have ha_ne : a ≠ 0 := by
    intro h
    exact hzero (h ▸ ha)
  have ha_pos : (0 : ℚ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha_ne)
  have hn_nat : 1 < A.card := Nat.lt_of_succ_le hcard
  have hn : (1 : ℚ) < A.card := by exact_mod_cast hn_nat
  exact (not_le_of_gt (div_lt_self ha_pos hn)) hbound

end JSP331
