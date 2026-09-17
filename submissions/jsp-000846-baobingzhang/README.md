# JSP-000846: Erdős 1016, Bondy's lower bound h(n) ≥ log₂(n−1) − 1 for pancyclic graphs

Catalog entry: [JSP-000846](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000846) · Problem source: [erdosproblems.com/1016](https://www.erdosproblems.com/1016)

## Problem

Let `h(n)` be minimal such that there is a graph on `n` vertices with `n + h(n)` edges which contains a cycle on `k` vertices for all `3 ≤ k ≤ n` (a pancyclic graph). Estimate `h(n)`. In particular, is `h(n) ≥ log₂ n + log_* n − O(1)`?

## Scope

Partial progress: the known lower bound `log₂(n−1) − 1 ≤ h(n)` stated by Bondy [Bo71] (proof first given by Griffin [Gr13]), as recorded on erdosproblems.com/1016. The matching upper bound `h(n) ≤ log₂ n + log_* n + O(1)` (George–Khodkar–Wallis) is not formalized, and the actual question — whether `h(n) ≥ log₂ n + log_* n − O(1)`, or even `h(n) − log₂ n → ∞` — remains open and is not addressed.

## Formal statements

All results are in `Erdos1016.lean`. No formal-conjectures statement exists for #1016 (erdosproblems lists 'Formalised statement? No'). Definitions follow the problem text literally; `h` is computed in ℤ to avoid truncated subtraction, `h_spec` proves it is the attained minimum and `isPancyclic_top` shows the set is nonempty. For `n < 3` pancyclicity is vacuous; all bounds assume `n ≥ 3`.

```lean
theorem card_sub_one_le_two_pow [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (hG : IsPancyclic G) :
    Fintype.card V - 1 ≤ 2 ^ (#G.edgeFinset + 1 - Fintype.card V)

theorem add_logb_le_card_edgeFinset [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (hG : IsPancyclic G) :
    (Fintype.card V : ℝ) + Real.logb 2 (Fintype.card V - 1) - 1 ≤ #G.edgeFinset

theorem pancyclic_edge_lower_bound (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : IsPancyclic G) :
    n - 1 ≤ 2 ^ (#G.edgeFinset + 1 - n) ∧
      (n : ℝ) + Real.logb 2 (n - 1) - 1 ≤ #G.edgeFinset

theorem logb_sub_one_le_h (n : ℕ) (hn : 3 ≤ n) : Real.logb 2 (n - 1) - 1 ≤ (h n : ℝ)

theorem sub_one_le_two_pow_h (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ h n ∧ n - 1 ≤ 2 ^ (h n + 1).toNat

theorem h_spec (n : ℕ) :
    (∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ (G.edgeSet.ncard : ℤ) = n + h n) ∧
      ∀ G : SimpleGraph (Fin n), IsPancyclic G → (n : ℤ) + h n ≤ G.edgeSet.ncard

theorem isPancyclic_top (n : ℕ) : IsPancyclic (⊤ : SimpleGraph (Fin n))

theorem not_isPancyclic_bot : ¬ IsPancyclic (⊥ : SimpleGraph (Fin 3))

theorem hasCycleOfLength_iff_cycleGraph_isContained (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k) :
    HasCycleOfLength G k ↔ (SimpleGraph.cycleGraph k).IsContained G
```

With `HasCycleOfLength G k := ∃ v, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = k`, `IsPancyclic G := ∀ k, 3 ≤ k → k ≤ card V → HasCycleOfLength G k`, `minPancyclicEdges n := sInf {m | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ G.edgeSet.ncard = m}` and `h n : ℤ := minPancyclicEdges n − n`: `card_sub_one_le_two_pow` (every pancyclic graph on `n ≥ 3` vertices with `m` edges has `n − 1 ≤ 2^(m+1−n)`), `add_logb_le_card_edgeFinset` (`n + log₂(n−1) − 1 ≤ m`, real form), `pancyclic_edge_lower_bound` (both forms on `Fin n`), `logb_sub_one_le_h` (`log₂(n−1) − 1 ≤ h(n)` for `n ≥ 3`), `sub_one_le_two_pow_h`, and sanity lemmas `h_spec` (h is exactly the minimum, attained), `isPancyclic_top` (the minimised set is nonempty), `not_isPancyclic_bot`, `hasCycleOfLength_iff_cycleGraph_isContained` (cycle definition agrees with containing a copy of `C_k`).

## Proof outline

Take a Hamiltonian cycle and delete one edge to get a path `P` with `n − 1` edges; let `R = E(G) \ E(P)`, so `|R| = m − n + 1`. Map each length `k ∈ [3, n]` to `E(C_k) ∩ R` for a chosen `k`-cycle `C_k`. Every vertex has even degree in a cycle, and a nonempty edge set contained in a path has a vertex of degree one; hence `E(C_k) ∩ R ≠ ∅` and, if two cycles have the same `R`-part, the symmetric difference of their edge sets is an even-degree subset of `P`, hence empty, so the cycles have the same edge set and the same length. Thus `n − 2 ≤ 2^|R| − 1`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1016.card_sub_one_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.add_logb_le_card_edgeFinset' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.pancyclic_edge_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.logb_sub_one_le_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.sub_one_le_two_pow_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.h_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.isPancyclic_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.not_isPancyclic_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1016.hasCycleOfLength_iff_cycleGraph_isContained' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1016.lean` (`0acf41603148de2fc730132d2beae7b2d058489ba69853c6c92e1a0e2050f8b7`) are in `verification/`.

## Attribution

- Mathematics: J. A. Bondy, Pancyclic graphs I, J. Combin. Theory Ser. B 11 (1971) [Bo71] (bound stated without details); M. Griffin, Minimal pancyclicity (2013) [Gr13] (first proof); problem of Erdős [Er71], erdosproblems.com/1016. The Lean proof uses the standard edge-set injection argument reconstructed independently (Griffin's paper was not consulted), written with AI assistance (Anthropic Claude).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
