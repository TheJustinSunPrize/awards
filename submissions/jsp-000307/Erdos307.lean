/-
JSP-000307: Can three consecutive integers have strictly decreasing largest
prime factors?

Answer: Yes. Balasubramanian (2001) proved that infinitely many such triples
exist. The simplest example is (13, 14, 15):

  maxPrimeFac 13 = 13  (13 is prime)
  maxPrimeFac 14 = 7   (14 = 2 × 7)
  maxPrimeFac 15 = 5   (15 = 3 × 5)

and 13 > 7 > 5.

This file formalizes the existential witness n = 13 as a scoped component of
the solved problem.

References:
  [ErPo78] Erdős and Pomerance, "On the largest prime factors of n and n+1",
           Aequationes Math. 16 (1978), 311–321.
  [Ba01]   Balasubramanian, "On triplets with descending largest prime factors",
           Studia Sci. Math. Hungar. 36 (2001), 45–50.
-/

import Mathlib.Data.Nat.MaxPrimeFac

open Nat

/-- JSP-000307: There exist three consecutive positive integers whose largest
prime factors are strictly decreasing.

The witness is n = 13:
  maxPrimeFac 13 = 13
  maxPrimeFac 14 = 7
  maxPrimeFac 15 = 5

This resolves the existential question (the answer is yes). The proof that
infinitely many such triples exist [Ba01] is outside the scope of this
formalization. -/
theorem jsp_000307 : ∃ n : ℕ, 1 < n ∧
    maxPrimeFac n > maxPrimeFac (n + 1) ∧
    maxPrimeFac (n + 1) > maxPrimeFac (n + 2) := by
  -- We use the witness n = 13.
  -- 13 is prime, so maxPrimeFac 13 = 13.
  -- 14 = 2 * 7, so maxPrimeFac 14 = 7.
  -- 15 = 3 * 5, so maxPrimeFac 15 = 5.
  refine ⟨13, by decide, ?_, ?_⟩
  · -- maxPrimeFac 13 = 13 and maxPrimeFac 14 = 7
    -- 13 is prime: maxPrimeFac 13 = 13
    have h13 : maxPrimeFac 13 = 13 := by
      rw [show maxPrimeFac 13 = maxPrimeFac (13 : ℕ) from rfl]
      exact (by decide : (13 : ℕ).Prime).maxPrimeFac_eq_self
    -- 14 = 2 * 7, maxPrimeFac 14 = 7
    have h14 : maxPrimeFac 14 = 7 := by
      rw [show (14 : ℕ) = 2 * 7 from by decide]
      rw [maxPrimeFac_mul (by decide) (by decide)]
      rw [(by decide : (2 : ℕ).Prime).maxPrimeFac_eq_self]
      rw [(by decide : (7 : ℕ).Prime).maxPrimeFac_eq_self]
      decide
    rw [h13, h14]
    decide
  · -- maxPrimeFac 14 = 7 and maxPrimeFac 15 = 5
    have h14 : maxPrimeFac 14 = 7 := by
      rw [show (14 : ℕ) = 2 * 7 from by decide]
      rw [maxPrimeFac_mul (by decide) (by decide)]
      rw [(by decide : (2 : ℕ).Prime).maxPrimeFac_eq_self]
      rw [(by decide : (7 : ℕ).Prime).maxPrimeFac_eq_self]
      decide
    -- 15 = 3 * 5, maxPrimeFac 15 = 5
    have h15 : maxPrimeFac 15 = 5 := by
      rw [show (15 : ℕ) = 3 * 5 from by decide]
      rw [maxPrimeFac_mul (by decide) (by decide)]
      rw [(by decide : (3 : ℕ).Prime).maxPrimeFac_eq_self]
      rw [(by decide : (5 : ℕ).Prime).maxPrimeFac_eq_self]
      decide
    rw [h14, h15]
    decide
