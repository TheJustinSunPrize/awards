/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-001007 (Green's open problem 44 / Erdős problem #1202): formal statement package

Catalog question (JSP-001007, `problems/catalog-1001-1022.md`):

> How many integers can simultaneously avoid about half the residue classes modulo each of
> several primes?

Pinned sources:

* Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math. (1980)
  89–115, Section 6, Problem 3.
* Ben Green, *100 open problems*, Problem 44
  (<https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf>):
  "Sieve `[N]` by removing half the residue classes mod `p_i`, for primes
  `2 ≤ p_1 < ⋯ < p_1000 < N^{9/10}`.  Does the remaining set have size at most `N/10`?"
* <https://www.erdosproblems.com/1202> (Erdős problem #1202, the related general
  sieve question). The formal definitions below use the diagonal `ε = 1/10`
  specialization sufficient for the negative answer.
* Resolution (negative), by Price and GPT-5.4 Pro:
  <https://www.overleaf.com/read/qyhdmrchqnvb>.  The construction takes the `A_i` to be
  intervals, and the surviving set contains a long arithmetic progression: for every `c > 0`
  and `m > √(n log n)` there are `k ≫_c m² / (n log n)` primes `m < p_1 < ⋯ < p_k ≤ 2m`,
  each with `(p_i-1)/2` classes, such that at least `(1/2 - c)n` integers in `[1,n]` avoid
  all the `A_i`.
* The *statement* of Green's problem 44 is already formalized (with `answer(sorry)`) in
  Google DeepMind's `formal-conjectures`:
  `FormalConjectures/GreensOpenProblems/44.lean`, namespace `Green44`.

This file defines the surviving set, a diagonal specialization of the conjecture,
and the stronger arbitrarily-large-counterexample statement. The complete counterexample
is proved in `Jsp.Jsp001007Final`; its implication for the recorded conjecture, including
`k = 0` and conversion of the numerical bounds, is proved in `Jsp.Jsp001007Conclusion`.
-/

import Mathlib

namespace JSP001007

/-- The set of `m ∈ [1, n]` avoiding every `A_i` modulo `p_i`. -/
def survivors (n : ℕ) {k : ℕ} (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))) :
    Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ i, (m : ZMod (p i)) ∉ A i

/-- The hypothesis that `p` lists `k` primes below `n ^ (1-ε)` in strictly increasing order,
each with `(p_i - 1)/2` removed classes. -/
def AdmissibleConfig (ε : ℝ) (n k : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Prop :=
  (∀ i, (p i).Prime) ∧ StrictMono p ∧
    (∀ i, (A i).card = (p i - 1) / 2) ∧
    (∀ i, ((p i : ℝ) < (n : ℝ) ^ (1 - ε)))

/-- **Erdős problem #1202 / Green problem 44 (conjecture, now known to be false).**
For a fixed `ε`, there is `k` such that every admissible configuration of `k` primes
below `n^{1-ε}` leaves at most `ε n` survivors. This is a one-parameter diagonal
specialization; the negative case `ε = 1/10` suffices for the conjecture's refutation. -/
def Green44Conjecture (ε : ℝ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, ∀ (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
    AdmissibleConfig ε n k p A → (survivors n p A).card ≤ ε * n

/-- **A stronger arbitrarily-large-counterexample statement.**  For the refutation of
the conjecture: for every `k` there are arbitrarily large `n` and an admissible configuration
of `k` primes together with classes that leave **more** than `ε n` survivors. -/
def Green44Refutation (ε : ℝ) : Prop :=
  ∀ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      AdmissibleConfig ε n k p A ∧ ε * n < (survivors n p A).card

/-- Arbitrarily large counterexamples imply the negation of the recorded conjecture. -/
theorem refutation_implies_not_conjecture (ε : ℝ) (h : Green44Refutation ε) :
    ¬ Green44Conjecture ε := by
  intro hc
  obtain ⟨k, hk⟩ := hc
  obtain ⟨n, _, p, A, hconf, hgt⟩ := h k 0
  exact absurd (hk n p A hconf) (not_le.mpr hgt)

end JSP001007
