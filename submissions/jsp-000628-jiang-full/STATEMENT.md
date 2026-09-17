# Statement correspondence

## Original result

For positive `k`, let `g_k(n)` be the largest number of edges in an
`n`-vertex graph with no cycle having `k` distinct chords incident to a
single cycle vertex. Jiang proved that, when `n ≥ 3k + 3`,

`g_k(n) = (k + 1)n - (k + 1)^2`.

## Lean statement

`HasCycleWithKIncidentChords k G` gives a cycle, a common vertex `v`, and an
injective map `Fin k → V` whose images are the opposite endpoints of `k`
chords incident to `v`. Injectivity makes the chord edges distinct.

`chordCycleExtremalNumber k n` is the maximum edge count among admissible
simple graphs labelled by `Fin n`. Every finite simple graph on `n` vertices
is represented up to isomorphism by such a labelled graph.

`Erdos767.erdos_767` proves the displayed equality under exactly `0 < k` and
`3 * k + 3 ≤ n`. Thus it formalizes both the upper bound and the matching
complete-bipartite lower construction in Jiang's theorem.

## Scope

This package proves the original 2004 theorem recorded in JSP-000628. It does
not claim the stronger 2026 Chen--Ning formula for all `n ≥ k + 2`.
