# Candidate observation

## English

This candidate observation is associated with [JSP-000872 — Are there only finitely many unitary perfect numbers, equal to the sum of their proper divisors coprime to their complementary divisors?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000872). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean 4 formalization proving that 6, 60 and 90 are unitary perfect numbers: the sum of the unitary divisors of `n` (divisors `d | n` with `gcd d (n / d) = 1`) equals `2 * n` for `n = 6` (`1 + 2 + 3 + 6 = 12`), `n = 60` (`1 + 3 + 4 + 5 + 12 + 15 + 20 + 60 = 120`), and `n = 90` (`1 + 2 + 5 + 9 + 10 + 18 + 45 + 90 = 180`). The formal source is pinned to the public repository [Yaohua-Leo/jsp-000872-lean](https://github.com/Yaohua-Leo/jsp-000872-lean), commit `3f267ab529a75259abcfd0ef771d47add428782d`, built with Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2`.

**Claim boundary: witness-only component.** This observation records a complete, machine-checked Lean proof that 6, 60 and 90 are unitary perfect numbers. The finiteness question asked by the catalog entry is not addressed, the catalogued problem is not resolved, and no award claim is made.

A local Lean compilation (`lake env lean JSP000872.lean`, zero errors) and an axiom audit (`#print axioms` reporting only `propext, Classical.choice, Quot.sound` for every theorem) were run with the pinned toolchain. These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
