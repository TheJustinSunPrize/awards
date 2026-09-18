/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000639 — Observation record: explicit prime pairs `(q, q + P)` with
`q` strictly between the largest factor and the primorial `P`, for the
products `P` of the first `k` primes with `k = 2, 3, 4, 5`.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0601-0700.md,
#JSP-000639):
  "For a product of the first several primes, is there always a prime
   between its largest factor and the product whose sum with the product
   is also prime?"

Scope of this file
------------------
This file records complete, machine-checked Lean proofs of explicit
witnesses for `k = 2, 3, 4, 5`:

  k = 2: `P = 2 * 3 = 6`,       `q = 5`,  `q + P = 11`
  k = 3: `P = 2 * 3 * 5 = 30`,  `q = 7`,  `q + P = 37`
  k = 4: `P = 2 * 3 * 5 * 7 = 210`,  `q = 13`, `q + P = 223`
  k = 5: `P = 2 * 3 * 5 * 7 * 11 = 2310`, `q = 23`, `q + P = 2333`

For each `k` the witness `q` is prime, strictly between the largest prime
factor `p_k` of `P` and `P` itself, and `q + P` is prime.

It does NOT assert the property for all `k`, does not resolve the
catalogued open problem (which remains Open), and makes no award claim.

Mathematical area: Number theory / Primes.
Problem posed: no later than 1983 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- The primorial construction of the catalog question: the product of a
list of primes `ps` (for the problem, the list of the first `k` primes). -/
def primorialOf (ps : List ℕ) : ℕ := ps.prod

/-- **Explicit witness for JSP-000639, k = 2.**

With `P = 2 * 3 = 6` (product of the first two primes), the prime `q = 5`
satisfies `3 < 5 < 6`, where `3` is the largest prime factor of `P`, and
`q + P = 5 + 6 = 11` is prime. -/
theorem jsp000639_k2 :
    (∀ p ∈ [2, 3], Nat.Prime p) ∧ primorialOf [2, 3] = 6 ∧
      Nat.Prime 5 ∧ 3 < 5 ∧ 5 < 6 ∧ Nat.Prime (5 + 6) := by
  decide

/-- **Explicit witness for JSP-000639, k = 3.**

With `P = 2 * 3 * 5 = 30` (product of the first three primes), the prime
`q = 7` satisfies `5 < 7 < 30`, where `5` is the largest prime factor of
`P`, and `q + P = 7 + 30 = 37` is prime. -/
theorem jsp000639_k3 :
    (∀ p ∈ [2, 3, 5], Nat.Prime p) ∧ primorialOf [2, 3, 5] = 30 ∧
      Nat.Prime 7 ∧ 5 < 7 ∧ 7 < 30 ∧ Nat.Prime (7 + 30) := by
  decide

set_option maxRecDepth 8000 in
/-- **Explicit witness for JSP-000639, k = 4.**

With `P = 2 * 3 * 5 * 7 = 210` (product of the first four primes), the
prime `q = 13` satisfies `7 < 13 < 210`, where `7` is the largest prime
factor of `P`, and `q + P = 13 + 210 = 223` is prime. -/
theorem jsp000639_k4 :
    (∀ p ∈ [2, 3, 5, 7], Nat.Prime p) ∧ primorialOf [2, 3, 5, 7] = 210 ∧
      Nat.Prime 13 ∧ 7 < 13 ∧ 13 < 210 ∧ Nat.Prime (13 + 210) := by
  decide

set_option maxRecDepth 8000 in
/-- **Explicit witness for JSP-000639, k = 5.**

With `P = 2 * 3 * 5 * 7 * 11 = 2310` (product of the first five primes),
the prime `q = 23` satisfies `11 < 23 < 2310`, where `11` is the largest
prime factor of `P`, and `q + P = 23 + 2310 = 2333` is prime. -/
theorem jsp000639_k5 :
    (∀ p ∈ [2, 3, 5, 7, 11], Nat.Prime p) ∧
      primorialOf [2, 3, 5, 7, 11] = 2310 ∧
      Nat.Prime 23 ∧ 11 < 23 ∧ 23 < 2310 ∧ Nat.Prime (23 + 2310) := by
  decide

/-- The same values arise from Mathlib's primorial `n#`, the product of
the primes `≤ n`: for `p` the `k`-th prime, `p#` is the product of the
first `k` primes, so the witnesses above live exactly at `3#`, `5#`,
`7#` and `11#`. -/
theorem jsp000639_mathlib_primorial_values :
    primorial 3 = 6 ∧ primorial 5 = 30 ∧ primorial 7 = 210 ∧
      primorial 11 = 2310 := by
  decide

/-- **Total form of the observation, instantiated.**

There exists a list of primes `ps` and a prime `q` with every factor of
`ps.prod` strictly below `q`, `q` strictly below `ps.prod`, and `q +
ps.prod` prime — here `ps = [2, 3]`, `q = 5`. This is the `k = 2`
instance of the catalog question phrased as a single existential; it is
not a proof of the question's universally quantified reading. -/
theorem jsp000639_exists :
    ∃ ps : List ℕ, ∃ q : ℕ,
      (∀ p ∈ ps, Nat.Prime p) ∧ (∀ p ∈ ps, p < q) ∧
        Nat.Prime q ∧ q < ps.prod ∧ Nat.Prime (q + ps.prod) := by
  refine ⟨[2, 3], 5, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

#print axioms jsp000639_k2
#print axioms jsp000639_k3
#print axioms jsp000639_k4
#print axioms jsp000639_k5
#print axioms jsp000639_mathlib_primorial_values
#print axioms jsp000639_exists
