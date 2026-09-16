# Candidate observation

## English

This preliminary observation is associated with [JSP-000884 — How does an integer's totient compare with the totient of the integer minus its totient?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000884). It publishes `Statement.lean` and `Proof.lean` for the reverse-inequality infinitude component: the set of natural numbers `n` satisfying `totient n < totient (n - totient n)` is infinite, as recorded in the public [Erdos Problem #1064](https://www.erdosproblems.com/1064) source. **Claim boundary: partial result.** The theorem covers this reverse-inequality infinitude component only; it does not formalize every comparison or component encompassed by the broader catalog question.

A local Lean compilation was run with Lean 4.33.1 and the pinned Mathlib revision. That compiler result is only a reproducibility check; it is not independent verification of statement faithfulness or official JSP verification.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
