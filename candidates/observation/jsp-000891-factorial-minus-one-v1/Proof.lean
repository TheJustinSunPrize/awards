/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000891 — Observation record: how small can the first factorial index
congruent to minus one modulo a prime be?

Catalog question (TheJustinSunPrize/awards, problems/catalog-0801-0900.md,
#JSP-000891):
  "How small can the first factorial index congruent to minus one modulo a
   prime be?"

Scope of this file
------------------
Wilson's theorem gives `(p-1)! ≡ -1 (mod p)` for every prime `p`, so for each
prime `p` there is a first index `n` with `n! ≡ -1 (mod p)` and it is at most
`p - 1`.  This file records a complete, machine-checked Lean proof that this
first index can be far smaller than the Wilson index `p - 1`, by verifying
primality, the congruence, and the minimality of the index for three explicit
instances:

* `(n, p) = (3, 7)`:  `3! = 6 ≡ -1 (mod 7)`, and `0! = 1! = 1`, `2! = 2` are
  not congruent to `-1 (mod 7)`;
* `(n, p) = (5, 11)`: `5! = 120 ≡ -1 (mod 11)`, and `0! = 1! = 1`, `2! = 2`,
  `3! = 6`, `4! = 24` are not congruent to `-1 (mod 11)`;
* `(n, p) = (7, 71)`: `7! = 5040 = 71² - 1 ≡ -1 (mod 71)`, and `0! = 1! = 1`,
  `2! = 2`, `3! = 6`, `4! = 24`, `5! = 120`, `6! = 720` are not congruent to
  `-1 (mod 71)`.

It does NOT assert anything for all primes, does not address the distribution
question (whether such small indices occur for infinitely many primes), does
not resolve the catalogued open problem, and makes no award claim.

Mathematical area: Number theory.
Problem posed: no later than 2002 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **JSP-000891 instance `(p, n) = (7, 3)`.** `7` is prime, `3! = 6 ≡ -1 (mod 7)`,
and no smaller factorial index is congruent to `-1 (mod 7)`. -/
theorem jsp000891_p7 :
    Nat.Prime 7 ∧ Nat.factorial 3 % 7 = 6 ∧ (∀ m < 3, Nat.factorial m % 7 ≠ 6) := by
  decide

/-- **JSP-000891 instance `(p, n) = (11, 5)`.** `11` is prime, `5! = 120 ≡ -1 (mod 11)`,
and no smaller factorial index is congruent to `-1 (mod 11)`. -/
theorem jsp000891_p11 :
    Nat.Prime 11 ∧ Nat.factorial 5 % 11 = 10 ∧ (∀ m < 5, Nat.factorial m % 11 ≠ 10) := by
  decide

/-- **JSP-000891 instance `(p, n) = (71, 7)`.** `71` is prime, `7! = 5040 ≡ -1 (mod 71)`
(indeed `5040 = 71² - 1`), and no smaller factorial index is congruent to
`-1 (mod 71)`. -/
theorem jsp000891_p71 :
    Nat.Prime 71 ∧ Nat.factorial 7 % 71 = 70 ∧ (∀ m < 7, Nat.factorial m % 71 ≠ 70) := by
  decide

/-- **JSP-000891 observation (existence component, combined form).** There exist a
prime `p` and a factorial index `n` strictly below the Wilson index `p - 1` such
that `n! ≡ -1 (mod p)` and `n` is the *first* such index
(instance `(n, p) = (3, 7)`: `3! = 6 ≡ -1 (mod 7)`, strictly below `6 = 7 - 1`). -/
theorem jsp000891_observation :
    ∃ (n p : ℕ), Nat.Prime p ∧ n + 1 < p ∧
      Nat.factorial n % p = p - 1 ∧ (∀ m < n, Nat.factorial m % p ≠ p - 1) :=
  ⟨3, 7, by decide⟩

-- Axiom audit (decide proofs are expected to be axiom-free):
#print axioms jsp000891_p7
#print axioms jsp000891_p11
#print axioms jsp000891_p71
#print axioms jsp000891_observation
