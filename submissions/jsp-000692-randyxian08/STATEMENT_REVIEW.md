# Statement-to-problem review

This is a review checklist and mapping, not a signed independent review. `Statement.lean` prints the relevant definitions and checks the final theorem types during the recorded successful Lean run.

| Intended requirement | Actual definition or theorem |
| --- | --- |
| Finite hypergraph | `Hypergraph V := Finset (Finset V)`; final quantifiers use `V = Fin n` |
| Rank r, r ≥ 2 | `Uniform H r` requires `e.card = r` for every edge; final theorems require `2 ≤ r` |
| Intersecting | `Intersecting H` requires `(e ∩ f).Nonempty` for all edges; no hidden restriction to a subfamily |
| Colouring forbids monochromatic edges | `Proper H c` requires two differently coloured vertices in every edge |
| Chromatic number exactly 3 | `ThreeChromatic H` includes existence of a proper `Fin 3` colouring and nonexistence of a proper Boolean colouring |
| Active rather than padded ambient vertices | `support H := H.biUnion id`; the inequality counts `(support H).card` |
| Counterexample has no isolated vertices | `quadratic_counterexamples` explicitly includes `support H = Finset.univ` |
| Negate a genuine eventual Big-O bound | `QuadraticVertexBound` quantifies one real C>0 and one threshold R, then every eligible hypergraph of every r≥max(2,R) |
| Arbitrary coefficient and threshold | `quadratic_counterexamples C R` works for every real C and natural R, not just C=1 |
| Construction for all ranks | `alon_for_every_rank r hr` supplies a witness for every r≥2 with at least `2^(r-2)` active vertices |
| One positive constant in Question 2 | `LinearIntersectionAssertion` puts C>0 before the quantifiers r,n,H; `jsp000692_question_two` chooses 1/3 |
| Distinct witness edges | All final intersection assertions include `e ≠ f` explicitly |
| Stronger integer formulation | `large_intersection_nat` proves `r ≤ 2*(e ∩ f).card+1`; it does not incorrectly replace this by `r ≤ 2*(e ∩ f).card` |
| Both answers together | `jsp000692_complete` and `jsp000692_complete_explicit` |

## Dependency scope

The first part depends on the construction, its compiled properties, Boolean injection and growth induction. The second part depends on finite maximization, the opposite-edge lemma and matrix counting. The two branches share `Hypergraph.lean` but neither assumes the other branch's conclusion. All project lemma/theorem declarations are included in `Audit.lean`.

The finite Python checks are not imported into Lean. No externally claimed solution is added as an axiom. The final proof does not import an external problem file containing placeholders. The standalone form imports only the pinned mathlib.

## Boundaries requiring reviewers

The source is authored for finite hypergraphs, matching the `Fin n` formal statement used here. It does not claim a separate compactness argument for arbitrary infinite edge families. It does not formalize the exact central-binomial vertex count or a best-possible asymptotic intersection constant, neither of which is needed to answer the stated two finite questions.

A reviewer must still compile the source, inspect the resulting theorem types and axiom dependencies, and decide whether the two finite statements cover the prize entry's intended scope. A successful build does not determine priority, attribution, award eligibility or payment.

## Current review outcomes

Local Lean compilation and all 67 theorem axiom audits: **passed**, including the standalone version. The final source hashes are recorded in the publication review receipt.

Statement and mathematical argument: reviewed locally with Codex assistance; this is submitter-produced evidence, not independent human review. Priority and organizer review remain outstanding. Submission does not establish award approval or payment.
