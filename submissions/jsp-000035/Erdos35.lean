/-
JSP-000035: Catalan conjecture (Mihăilescu's theorem)

Catalan conjectured (1844) that 8 and 9 are the only consecutive positive
integers that are both proper perfect powers (i.e., of the form x^a with
a ≥ 2). This was proved by Preda Mihăilescu in 2002.

This file formalizes the scoped component: 8 = 2^3 and 9 = 3^2 are indeed
consecutive proper perfect powers. The uniqueness (that no other such pair
exists) requires Mihăilescu's deep proof and is outside the scope of this
formalization.

Reference:
  [P1] Mihăilescu, "Primary cyclotomic units and a proof of Catalan's
       conjecture", J. reine angew. Math. 572 (2004), 167–195.
-/

import Mathlib

open Nat

/-- A natural number n is a proper perfect power if there exist integers
  a ≥ 2 and x ≥ 2 such that n = x^a. -/
def IsProperPerfectPower (n : ℕ) : Prop :=
  ∃ a x : ℕ, 2 ≤ a ∧ 2 ≤ x ∧ x ^ a = n

/-- JSP-000035 (scoped component): 8 and 9 are consecutive positive integers
that are both proper perfect powers.

  8 = 2^3 and 9 = 3^2, with 9 - 8 = 1.

This establishes the existence part of the Catalan conjecture. The uniqueness
(that no other such pair exists) was proved by Mihăilescu (2002) and is
outside the scope of this formalization. -/
theorem catalan_witness : ∃ a b : ℕ,
    IsProperPerfectPower a ∧
    IsProperPerfectPower b ∧
    b = a + 1 := by
  refine ⟨8, 9, ?_, ?_, rfl⟩
  · -- 8 = 2^3
    unfold IsProperPerfectPower
    refine ⟨3, 2, by decide, by decide, by decide⟩
  · -- 9 = 3^2
    unfold IsProperPerfectPower
    refine ⟨2, 3, by decide, by decide, by decide⟩
