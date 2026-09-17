# Candidate observation

## English

This local observation is associated with the historical tournament wording for [JSP-001021 — How large a transitive subtournament must every tournament of prescribed order contain?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001021). It formalizes Moon's all-quantifier lower-bound theorem for the number of transitive subtournaments: for every finite tournament `T` and every `k`, the number of transitive `k`-subtournaments is at least

\[
\tau(n,k)=
\begin{cases}
\displaystyle\prod_{i=0}^{k-1}\frac{n-(2^i-1)}{2^i},& n>2^{k-1}-1,\\
0,& n\le 2^{k-1}-1.
\end{cases}
\]

The bound is Theorem 4 of J. W. Moon, [*On Subtournaments of a Tournament*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5D7CCBE66AB07BB3F90F771D1CD3CD08/S0008439500052875a.pdf/on-subtournaments-of-a-tournament.pdf), *Canadian Mathematical Bulletin* 9 (1966), 297–301. The Lean development proves the source count recurrence by the unique source vertex, the score-sum identity, and the convexity/Jensen inequality for Moon's product. The previous power-of-two existence theorem is a corollary of the positive lower bound.

**Statement-identity warning.** The currently provisioned contract `problem:erdosproblems-1021` instead records the extremal-number question for the bipartite graph obtained by subdividing each edge of `K_k`. Consequently this Moon theorem is not an exact formalization of that current contract, and it must not be promoted to a complete JSP-001021 solution without an adjudicated contract/source correction.

A local replay uses Lean 4.33.1 and the pinned Mathlib revision; compilation alone is not independent verification, official JSP verification, or an award decision. The observation remains candidate-only.
