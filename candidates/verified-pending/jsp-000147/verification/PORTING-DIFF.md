# Porting diff — JSP-000147 (mathlib v4.33.0 -> v4.34.0)

Pinned source: plby/lean-proofs @ 1268917deaaaa0d674f651287027baa26cea9920
(clone of OpenAI ten-proofs CompactnessAndDegeneracy development, ported by
plby to mathlib v4.33.0). Verification target: mathlib v4.34.0
(commit 5ed2965256430c3649e86755f9576b54eca72435), Lean v4.34.0.

Exactly one line of the 7-file closure (381,239 bytes total) required change:

## File: ErdosProblems/Erdos146/BinaryEntropy.lean (line 2068)

- old: `apply Finset.prod_le_prod`
- new: `apply Finset.prod_le_prod₀`

rationale: In mathlib 4.34, `Finset.prod_le_prod` acquired an explicit
`[MulLeftMono N]` typeclass requirement, which cannot be synthesized for `ℝ`
(left multiplication by negative scalars is not monotone). The intended
ordered-ring replacement `Finset.prod_le_prod₀` takes the hypotheses
`∀ i ∈ s, 0 ≤ f i` and `∀ i ∈ s, f i ≤ g i` — exactly the two branches already
present in the original proof (`positivity`, and
`choose_le_exp_binary_entropy`). Semantics unchanged; no axiom added.

All other errors in the first compile run were cascading failures from this
single missing olean.