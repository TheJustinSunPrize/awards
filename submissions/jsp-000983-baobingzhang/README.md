# JSP-000983: Erdős 1178, the Brown–Erdős–Sós lower bound d_r(e) ≥ (r−2)e+3 for all r, e ≥ 3

Catalog entry: [JSP-000983](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000983) · Problem source: [erdosproblems.com/1178](https://www.erdosproblems.com/1178)

## Problem

For `r ≥ 3` let `d_r(e)` be the minimal `d` such that `ex_r(n, 𝓕) = o(n²)`, where `𝓕` is the family of `r`-uniform hypergraphs on `d` vertices with `e` edges. Prove that `d_r(e) = (r−2)e + 3` for all `r, e ≥ 3`.

## Scope

Partial progress: the lower bound `d_r(e) ≥ (r−2)e+3` of Brown, Erdős and Sós (1973), i.e. one of the two inequalities of the conjecture, for all `r, e ≥ 3`, with an explicit quadratic lower bound on the extremal number. The upper bound `d_r(e) ≤ (r−2)e+3` (the Brown–Erdős–Sós conjecture proper; known only in special cases such as Ruzsa–Szemerédi and Erdős–Frankl–Rödl) is not formalized or claimed.

## Formal statements

All results are in `Erdos1178.lean`. formal-conjectures has no file for Erdős 1178; the definitions follow the erdosproblems.com wording and were cross-checked against the statement-only file `Statements/Erdos1178BrownErdosSosThreshold.lean` in WoshuaJolk/jig-verifier (same encoding; `sSup` in place of `Finset.sup`; no proof code copied). Copies are not necessarily induced.

```lean
theorem erdos_1178_lower_bound (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) : (r - 2) * e + 3 ≤ d_r r e

theorem erdos_1178_not_isSubquadratic (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    ∀ d ≤ (r - 2) * e + 2, ¬ IsSubquadratic r d e

theorem ex_lower_bound (r e : ℕ) (hr : 2 ≤ r) (he : 2 ≤ e) {d : ℕ} (hd : d ≤ (r - 2) * e + 2)
    {n : ℕ} (hn : 2 * r ≤ n) : (n : ℝ) ^ 2 / besConst r e ≤ ex r d e n

theorem family_nonempty (r e : ℕ) (hr : 3 ≤ r) : (family r ((r - 2) * e + 2) e).Nonempty

theorem d_r_le (r e : ℕ) : d_r r e ≤ r * e

theorem exists_card_eq_ex (r d e n : ℕ) (he : 1 ≤ e) :
    ∃ G : Hypergraph n, IsUniform r G ∧ IsFamilyFree r d e G ∧ #G = ex r d e n

theorem card_le_ex {r d e n : ℕ} {G : Hypergraph n} (hu : IsUniform r G)
    (hf : IsFamilyFree r d e G) : #G ≤ ex r d e n
```

With `r`-uniform hypergraphs on `Fin n` (Finsets of `r`-subsets), `ex r d e n` the maximum number of edges of an `r`-uniform hypergraph containing no copy of any `r`-uniform hypergraph on `d` vertices with `e` edges (`card_le_ex`, `exists_card_eq_ex`: a genuine maximum), `IsSubquadratic r d e` (`ex r d e n = o(n²)`) and `d_r r e := sInf {d | IsSubquadratic r d e}` (nonempty: `d_r_le : d_r r e ≤ r·e`): `ex_lower_bound : n²/besConst r e ≤ ex r d e n` for `d ≤ (r−2)e+2` and `n ≥ 2r` with an explicit constant, `erdos_1178_not_isSubquadratic : ∀ d ≤ (r−2)e+2, ¬ IsSubquadratic r d e`, and `erdos_1178_lower_bound : (r−2)e+3 ≤ d_r r e` for `r, e ≥ 3`. `family_nonempty` shows the forbidden family is nonempty at the critical `d`.

## Proof outline

Deletion method written as a weighted average: give each family `H` of `r`-subsets weight `p^|H|(1−p)^(N−|H|)`, so the expected number of edges is `pN` and a fixed configuration of `e` edges appears with weight `p^e`. The number of 'bad' configurations (`e` edges spanning at most `D = (r−2)e+2` vertices) is at most `A·n^D`. Some `H` has `|H| − e·#(bad configurations in H) ≥ pN − e·p^e·A·n^D`; deleting all edges of bad configurations leaves a hypergraph in which any `e` edges span more than `D` vertices. With `p = c/n^{r−2}` both terms scale like `n²`, and choosing `c` small gives `ex ≥ n²/besConst`. Monotonicity in `d` then gives the statement about `d_r`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1178.erdos_1178_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.erdos_1178_not_isSubquadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.ex_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.family_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.d_r_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.exists_card_eq_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1178.card_le_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1178.lean` (`d286f2ae31a4de88bbce3463f8be459033c284689698a15c6b2b67491b35d5b7`) are in `verification/`.

## Attribution

- Mathematics: W. G. Brown, P. Erdős, V. T. Sós, *Some extremal problems on r-graphs*, in New Directions in the Theory of Graphs (1973) 53–63 [BES73], credited on erdosproblems.com/1178 and in the catalog record JSP-000983. The standard deletion argument is presented here in averaged form, written during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
