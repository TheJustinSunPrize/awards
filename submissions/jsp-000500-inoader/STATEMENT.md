# Statement correspondence

## Original problem and specialization

[Erdős Problem 617](https://www.erdosproblems.com/617) asks whether, for every
r >= 3, every r-coloring of the edges of K_(r²+1) contains r+1 vertices on
whose induced edges some color is absent. The catalog mapping is
[JSP-000500](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000500).
The source paper is Erdős and Gyárfás, *Split and balanced colorings of complete
graphs*, Discrete Mathematics (1999), 79–86.

Here r = 7, r²+1 = 50, and r+1 = 8. The theorem proved is:

> For every finite vertex set V of cardinality 50 and every map from its
> unordered vertex pairs to seven colors, there exist a subset S of cardinality
> 8 and a color k such that every edge between distinct vertices of S has color
> different from k.

## Formal definitions

All definitions below are in [JSP500/Statement.lean](JSP500/Statement.lean).

| Formal object | Mathematical interpretation |
| --- | --- |
| `Fin 50` | A vertex set with exactly fifty elements |
| `Fin 7` | The seven available colors |
| `Sym2 V` | Unordered pairs of vertices, also permitting diagonal pairs |
| `c : Sym2 V → Fin 7` | An arbitrary undirected coloring; no surjectivity assumption |
| `S : Finset V`, `S.card = 8` | Eight distinct vertices |
| `Misses c S k` | Every pair of distinct vertices in S has color unequal to k |
| `Balanced c` | Every eight-vertex set contains an edge of each of the seven colors |

Although `Sym2` includes diagonal pairs, `Misses` explicitly requires `u ≠ v`.
Diagonal colors never constrain the conclusion. Every ordinary coloring of a
complete simple graph extends to a map on `Sym2`, so this encoding covers all
ordinary edge colorings.

`Main` is the exact proposition on `Fin 50`. `Upstream` universally quantifies
over finite types V with `Fintype.card V = 50`. Its existential conjunction
`∃ S, S.card = 8 ∧ ∃ k, Misses c S k` is logically equivalent to
`∃ S k, S.card = 8 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k`.

## Proof entry points

[JSP500/Main.lean](JSP500/Main.lean) proves:

```lean
theorem main_proven : Main
theorem upstream_proven : Upstream
```

Both are unconditional theorems. `no_balanced_fifty` rules out `Balanced c` for
any such coloring, and classical quantifier negation gives the required subset
and missing color. The intermediate use of a balanced coloring is a
contradiction assumption discharged by the final theorem.

This is a complete proof of the fixed r=7 specialization. It does not quantify
over other values of r. Definition correspondence is supplied here for human
review; the machine audit is recorded separately in [verification/axioms.log](verification/axioms.log).
