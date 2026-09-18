/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000332 — Observation record: sums of distinct factorials that are exact
prime powers.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0301-0400.md,
#JSP-000332):
  "How high a power of a prescribed prime can divide a sum of distinct
   factorials?"

Scope of this file
------------------
This file records complete, machine-checked Lean proofs of two explicit
existence witnesses for the observation

  "there is a sum of at least two distinct factorials that is *exactly* a
   prime power":

  * `2! + 3! + 4! = 2 + 6 + 24 = 32 = 2^5`, i.e. the sum of the factorials
    over the three-element index set `{2, 3, 4}` (a `Finset`, so the
    indices, and hence by injectivity of `Nat.factorial` the summands, are
    pairwise distinct) is exactly the fifth power of the prime `2`;
  * `1! + 2! + 4! = 1 + 2 + 24 = 27 = 3^3`, i.e. the sum of the factorials
    over the three-element index set `{1, 2, 4}` is exactly the third
    power of the prime `3`.

In both witnesses the displayed equation pins the exponent exactly — the
sum is *equal* to the prime power, no more and no less.  The condition
`2 ≤ T.card` excludes the trivial one-factorial case.

It does NOT answer the catalog question for a general prescribed prime
(it makes no statement about the *highest* power of a given prime dividing
a given sum of distinct factorials, nor about classification of all such
witnesses), does not resolve the catalogued open problem, and makes no
award claim.

Method
------
All numerical content is small enough to be discharged directly by
`decide` against the kernel computation of `Nat.factorial`, `Nat.pow` and
`Finset.sum` on literal finsets (`Nat.factorial 4 = 24` is well within
kernel reduction range).  No `sorry`, `admit`, `native_decide`, or added
unproved assumptions are used.

Mathematical area: Number theory / Factorials.
Problem posed: no later than 1980 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- **Existence witness (prime 2).** The sum of the factorials over the
index set `T = {2, 3, 4}`, which has at least two (pairwise distinct)
elements, is exactly the prime power `2^5`:
`2! + 3! + 4! = 2 + 6 + 24 = 32 = 2^5`. -/
theorem jsp000332_instance_two :
    ∃ (p e : ℕ) (T : Finset ℕ), 1 < p ∧
      p ^ e = T.sum (fun m => Nat.factorial m) ∧ 2 ≤ T.card :=
  ⟨2, 5, {2, 3, 4}, by decide, by decide, by decide⟩

/-- **Existence witness (prime 3).** The sum of the factorials over the
index set `T = {1, 2, 4}`, which has at least two (pairwise distinct)
elements, is exactly the prime power `3^3`:
`1! + 2! + 4! = 1 + 2 + 24 = 27 = 3^3`. -/
theorem jsp000332_instance_three :
    ∃ (p e : ℕ) (T : Finset ℕ), 1 < p ∧
      p ^ e = T.sum (fun m => Nat.factorial m) ∧ 2 ≤ T.card :=
  ⟨3, 3, {1, 2, 4}, by decide, by decide, by decide⟩

/-- **JSP-000332 observation.** Both witnesses together: there are (at
least) two distinct instances of a sum of at least two distinct factorials
that is exactly a prime power — `2! + 3! + 4! = 2^5` and
`1! + 2! + 4! = 3^3`.  This records the existence observation only; the
catalog question about the highest power of a prescribed prime dividing a
sum of distinct factorials remains open. -/
theorem jsp000332 :
    (∃ (p e : ℕ) (T : Finset ℕ), 1 < p ∧
       p ^ e = T.sum (fun m => Nat.factorial m) ∧ 2 ≤ T.card) ∧
    (∃ (p e : ℕ) (T : Finset ℕ), 1 < p ∧
       p ^ e = T.sum (fun m => Nat.factorial m) ∧ 2 ≤ T.card) :=
  ⟨jsp000332_instance_two, jsp000332_instance_three⟩

#print axioms jsp000332_instance_two
#print axioms jsp000332_instance_three
#print axioms jsp000332
