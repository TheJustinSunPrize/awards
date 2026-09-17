/-
Copyright (c) 2026 Yaohua-Leo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaohua-Leo (AI-assisted via ZCode (GLM))
-/
import Mathlib

/-!
# JSP-000872: Unitary perfect number witnesses 6, 60 and 90

This file records a complete, machine-checked proof that the numbers
6, 60 and 90 are *unitary perfect*: the sum of their unitary divisors
(divisors `d` of `n` with `gcd d (n / d) = 1`) equals `2 * n`.

**Scope.** This observation only witnesses the three concrete examples
above. The finiteness question asked by catalog entry JSP-000872 of
TheJustinSunPrize/awards ("Are there only finitely many unitary perfect
numbers?") is *not* addressed, the catalogued open problem is *not*
resolved, and no award claim is made.
-/

/-- The sum of the unitary divisors of `n`, i.e. the sum of all `d | n`
such that `d` and its complementary divisor `n / d` are coprime. -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Nat.gcd d (n / d) = 1)).sum (fun d => d)

/-- The unitary divisors of 6 are `{1, 2, 3, 6}`, summing to `12 = 2 * 6`;
hence 6 is unitary perfect. -/
theorem unitary_perfect_6 : unitaryDivisorSum 6 = 12 := by decide

/-- The unitary divisors of 60 are `{1, 3, 4, 5, 12, 15, 20, 60}`,
summing to `120 = 2 * 60`; hence 60 is unitary perfect. -/
theorem unitary_perfect_60 : unitaryDivisorSum 60 = 120 := by decide

/-- The unitary divisors of 90 are `{1, 2, 5, 9, 10, 18, 45, 90}`,
summing to `180 = 2 * 90`; hence 90 is unitary perfect. -/
theorem unitary_perfect_90 : unitaryDivisorSum 90 = 180 := by decide

/-- 6, 60 and 90 are unitary perfect numbers: the sum of their unitary
divisors equals twice the number. -/
theorem unitary_perfect_6_60_90 :
    unitaryDivisorSum 6 = 12 ∧ unitaryDivisorSum 60 = 120 ∧ unitaryDivisorSum 90 = 180 :=
  ⟨unitary_perfect_6, unitary_perfect_60, unitary_perfect_90⟩

-- Axiom audit: each `decide`-proved theorem is axiom-free (by `decide`),
-- and the conjunction is built purely from those.
#print axioms unitary_perfect_6
#print axioms unitary_perfect_60
#print axioms unitary_perfect_90
#print axioms unitary_perfect_6_60_90
