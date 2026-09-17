# Candidate observation

## English

This candidate observation is associated with [JSP-000139 — How large must the maximum degree of a triangle-free graph of diameter at most two be?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000139). It publishes `Statement.lean` and `Proof.lean` for the source-faithful formalization of Erdős Problem 133: if `f(n)` is the least maximum degree of an `n`-vertex triangle-free graph of diameter at most two, then for every `n ≥ 64`, `sqrt(n) - 1 ≤ f(n) ≤ 4*sqrt(n)`, hence `f(n) = Θ(sqrt(n))` and `f(n)/sqrt(n)` does not tend to infinity. The formal source is pinned to [Erdos133.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos133.lean), with the source record identifying David Hanson and Kathy Seyffarth for the mathematics and Codex/GPT-5.6 Sol for the formalization. **Claim boundary: complete theorem for this exact formalization.** It does not claim official JSP verification, award status, recipient identity, or independent review.

A local Lean compilation and trust-level-zero replay were run with Lean 4.33.1 and the pinned Mathlib revision. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
