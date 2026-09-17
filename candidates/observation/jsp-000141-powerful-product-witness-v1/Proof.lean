/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000141 — Observation record: explicit powerful product of consecutive
positive integers.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0101-0200.md,
#JSP-000141):
  "Can a product of consecutive positive integers have every prime factor
   occurring with exponent at least two?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the explicit
witness `8 * 9 = 72 = 2^3 * 3^2` for the literal yes/no reading of the
catalog question: the product `8 * 9` of the consecutive positive integers
`8` and `9` is a *powerful number* (every prime factor occurs with exponent
at least two).

It does NOT address stronger readings of the question (e.g. products of
three or more consecutive integers, or uniqueness/classification of such
witnesses), does not resolve the catalogued open problem, and makes no
award claim.

Mathematical area: Number theory / Powerful numbers.
Problem posed: no later than 1980 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **Explicit witness for JSP-000141 (literal yes/no reading).**

`8 * 9 = 72`, and every prime `p` dividing `72` satisfies `p^2 ∣ 72`:
indeed a prime dividing `8 = 2^3` must be `2`, and `2^2 ∣ 72`; a prime
dividing `9 = 3^2` must be `3`, and `3^2 ∣ 72`.  Thus `72 = 2^3 * 3^2`
is a powerful number that is a product of two consecutive positive
integers. -/
theorem powerful_product_witness :
    (8:ℕ) * 9 = 72 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ 72 → p ^ 2 ∣ 72 := by
  refine ⟨rfl, fun p hp h72 => ?_⟩
  rw [← show (8:ℕ) * 9 = 72 from rfl] at h72
  rcases (hp.dvd_mul).mp h72 with h8 | h9
  · -- a prime dividing 8 = 2^3 must be 2
    have h2 : p = 2 :=
      Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two
        (by rwa [show (2:ℕ) ^ 3 = 8 from rfl])
    subst h2
    norm_num
  · -- a prime dividing 9 = 3^2 must be 3
    have h3 : p = 3 :=
      Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three
        (by rwa [show (3:ℕ) ^ 2 = 9 from rfl])
    subst h3
    norm_num

#print axioms powerful_product_witness
