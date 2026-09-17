# JSP-000922: Erdős 1111 (El-Zahar–Erdős) for c ≤ 2: Wagon's bound d(t,2) ≤ C(t,2)+1, the recurrence d(t+1,2) ≤ d(t,2)+t, and d(3,2) = 4

Catalog entry: [JSP-000922](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000922) · Problem source: [erdosproblems.com/1111](https://www.erdosproblems.com/1111)

## Problem

Call disjoint vertex sets `A, B` anticomplete if there are no edges between them. If `t, c ≥ 1`, is there `d ≥ 1` such that every finite graph with `χ(G) ≥ d` and `ω(G) < t` has anticomplete sets `A, B` with `χ(A) ≥ χ(B) ≥ c`? (`d(t,c)` denotes the least such `d`.)

## Scope

Partial progress: the case `c ≤ 2` of the El-Zahar–Erdős problem, with the explicit bounds recorded on erdosproblems.com/1111 and credited in the catalog record JSP-000922: Wagon's `d(t,2) ≤ C(t,2)+1`, the recurrence `d(t+1,2) ≤ d(t,2)+t`, `d(2,2) = 2` and `d(3,2) = 4`, and `d(4,2) ≥ 5`. The general problem for `c ≥ 3` (El Zahar–Erdős bounds for `c = 3`, the Nguyen–Scott–Seymour theorem), the upper bound `d(4,2) ≤ 5` (Gaspers–Huang) and the reduction to `t ≤ c` are not formalized or claimed.

## Formal statements

All results are in `Erdos1111.lean`. formal-conjectures has no merged file for Erdős 1111; `IsAnticomplete`, `IsChromaticBound`, `d` and the theorem names follow the statement-only formal-conjectures PR #5892 (closed, not merged). The PR's recurrence statement is false for `t = 0`; the file proves this and uses `1 ≤ t`.

```lean
theorem erdos_1111_of_le_two (t c : ℕ) (ht : 1 ≤ t) (_hc : 1 ≤ c) (hc2 : c ≤ 2) :
    ∃ d ≥ 1, IsChromaticBound t c d

theorem erdos_1111.variants.wagon (t : ℕ) (_ht : 1 ≤ t) :
    IsChromaticBound t 2 (t.choose 2 + 1)

theorem isChromaticBound_three_two : IsChromaticBound 3 2 4

theorem erdos_1111.variants.wagon_recurrence (t : ℕ) (ht : 1 ≤ t) :
    d (t + 1) 2 ≤ d t 2 + t

theorem erdos_1111.variants.d_two_two : d 2 2 = 2

theorem erdos_1111.variants.d_three_two : d 3 2 = 4

theorem five_le_d_four_two : 5 ≤ d 4 2

theorem wagon {V : Type*} [Finite V] (G : SimpleGraph V) (h2 : TwoK2Free G) :
    G.Colorable ((G.cliqueNum + 1).choose 2)
```

With `IsAnticomplete`, `IsChromaticBound t c d` (every finite graph with `χ ≥ d` and no `K_t` has anticomplete `A, B` with `χ(G[A]), χ(G[B]) ≥ c`) and `d t c := sInf {n | IsChromaticBound t c n}`: `erdos_1111_of_le_two` (the problem's statement for `c ≤ 2`), `erdos_1111.variants.wagon : IsChromaticBound t 2 (C(t,2)+1)`, `isChromaticBound_three_two : IsChromaticBound 3 2 4`, `erdos_1111.variants.wagon_recurrence : 1 ≤ t → d (t+1) 2 ≤ d t 2 + t` (false for `t = 0`, which is also proved), `erdos_1111.variants.d_two_two : d 2 2 = 2`, `erdos_1111.variants.d_three_two : d 3 2 = 4`, `five_le_d_four_two`, and Wagon's colouring theorem `wagon : TwoK2Free G → G.Colorable (C(ω(G)+1, 2))`.

## Proof outline

For `c = 2`, anticomplete sets of chromatic number ≥ 2 exist iff the graph contains an induced `2K₂` (`exists_anticomplete_iff`). Wagon: take a maximum clique `K`; each vertex `u` misses a nonempty set `M(u) ⊆ K`; colour `u` by a pair `{x,y} ⊆ M(u)` (a singleton pair only if `M(u) = {x}`), using the `C(|K|+1,2)` elements of `K.sym2`. Adjacent vertices with the same singleton colour would enlarge the clique, and with the same pair `{x,y}` would form an induced `2K₂` with `xy`. Recurrence: choose `v` in a `t`-clique; its neighbourhood is `K_t`-free and needs fewer than `d(t,2)` colours, while non-neighbours are coloured by pairs `{v,y}` as in Wagon's argument. Lower bounds come from `C_5` (`d(3,2) ≥ 4`), the complement of `C_7` (`d(4,2) ≥ 5`) and a single vertex, checked by `decide`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1111.erdos_1111_of_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.erdos_1111.variants.wagon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.isChromaticBound_three_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.erdos_1111.variants.wagon_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.erdos_1111.variants.d_two_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.erdos_1111.variants.d_three_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.five_le_d_four_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1111.wagon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1111.lean` (`fdfc4d7c22ac37290c1175eebd440eac125f889f86c1744933a4fd8f74b8fe6c`) are in `verification/`.

## Attribution

- Mathematics: S. Wagon, *A bound on the chromatic number of graphs without certain induced subgraphs*, J. Combin. Theory Ser. B 29 (1980) 345–346 [Wa80b]; M. El-Zahar and P. Erdős, *On the existence of two nonneighboring subgraphs in a graph*, Combinatorica 5 (1985) 295–300 [ElEr85] (problem, and the recurrence and small values as recorded on erdosproblems.com/1111); both cited by the catalog record JSP-000922. The recurrence proof in the file was reconstructed during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
