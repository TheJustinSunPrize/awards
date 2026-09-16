# Comparison with the registered prior proof

The prior source is [Erdos833.lean at commit 8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean),
registered with reproduction evidence in [official issue #19](https://github.com/TheJustinSunPrize/awards/issues/19).
The mathematical result is credited to Paul Erdős and László Lovász.
The prior file credits Codex and GPT-5.6 Sol as formal authors. Our implementation
was developed separately with OpenAI Codex assistance for `xpzwzwz`.

| Aspect | Registered prior source | This repository |
| --- | --- | --- |
| Problem | Finite uniform hypergraph exponential degree bound | Same problem |
| Hypergraph | Finite set of finite vertex sets | Same mathematical objects |
| Two colours | `Fin 2` | `Bool`, an equivalent two-element type |
| Core method | Proved finite symmetric local lemma, dependency neighbours, conditional event counts | Direct growth of proper-colouring counts, recoverable monochromatic-edge compression, strong induction |
| Main explicit constant | `c = 1/9` | `c = 1/8` |
| Other degree bound | `2^(r-1)/(4*r)` | Strict bound `(2-β)*β^(r-2)` for every rational `β ≥ 1` |
| Assumptions | Final statement uses chromatic number three; helpers already cover non-two-colourability | Non-two-colourability throughout; in particular covers chromatic number three |
| Small ranks | Handled separately | Handled separately |
| Pinned environment | Source header: Lean/Mathlib 4.33.0 | Lean 4.34.0, fixed Mathlib revision |

Both solve the primary existential-constant question for finite hypergraphs.
Neither claims the exact extremal function for every rank. The different names
and colour types do not constitute a different mathematical problem or a broader
class than the prior proof's existing helper theorems.

Although `1/8 > 1/9`, this is only a comparison of the chosen explicit constants.
The prior classical bound is asymptotically stronger than our displayed
`(9/8)^r` bound (and the bound obtained by choosing `β=3/2`). We make no claim
of a new mathematical theorem, overall superiority, or first formalization.
The proposed contribution is a separately implemented counting proof and its
parameterized colouring criterion.

This comparison comes from reading the pinned prior source and its statements;
we have not independently rebuilt that prior repository. Its reproduction
results are reported by issue #19. Our own build and audit are in `evidence/`.
No prior Lean source is copied into this submission.
