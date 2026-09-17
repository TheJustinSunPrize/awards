# JSP-000184: Erdős 195, Adenwalla's bound: some permutation of ℤ has no monotone 5-term arithmetic progression (k ≤ 4)

Catalog entry: [JSP-000184](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000184) · Problem source: [erdosproblems.com/195](https://www.erdosproblems.com/195)

## Problem

What is the largest `k` such that every permutation of `ℤ` contains a monotone `k`-term arithmetic progression `x₁ < ⋯ < x_k`?

## Scope

Partial progress: Adenwalla's upper bound `k ≤ 4` (arXiv:2211.04451), the best known bound, which implies Geneson's `k ≤ 5`; these are the formal-conjectures variants `erdos_195.variants.leq_4_bound` and `leq_5_bound`. Whether the answer is 3 or 4 remains open and is not claimed; the lower bound `k ≥ 3` (Davis–Entringer–Graham–Simmons) is not formalized here.

## Formal statements

All results are in `Erdos195.lean`. `List.IsAPOfLengthWith`, `List.IsAPOfLength`, `HasMonotoneAP` (from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`) and the statements of `erdos_195.variants.leq_5_bound` and `leq_4_bound` (from `FormalConjectures/ErdosProblems/195.lean`) are copied verbatim from Google DeepMind's formal-conjectures project (Apache-2.0). As there, a permutation of `ℤ` is a bijection `ℕ ≃ ℤ` (a one-sided enumeration), which is the setting of Adenwalla's Theorem 1.

```lean
theorem erdos_195.variants.leq_4_bound :
    4 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}

theorem erdos_195.variants.leq_5_bound :
    5 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}

theorem not_hasMonotoneAP_perm {k : ℕ} (hk : 5 ≤ k) : ¬ HasMonotoneAP perm k

theorem exists_perm_not_hasMonotoneAP_five : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5

theorem le_four_of_mem {k : ℕ} (hk : k ∈ {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}) : k ≤ 4
```

`erdos_195.variants.leq_4_bound : 4 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}` and `erdos_195.variants.leq_5_bound` are proved with their exact formal-conjectures names and statements, using the formal-conjectures definitions `List.IsAPOfLengthWith`, `List.IsAPOfLength` and `HasMonotoneAP`. The file constructs an explicit `perm : ℕ ≃ ℤ` with `¬ HasMonotoneAP perm k` for all `k ≥ 5` (`not_hasMonotoneAP_perm`) and proves that every `k` in the set is at most 4 (`le_four_of_mem`), so the `sSup` is a genuine maximum of a bounded set rather than the junk value of an unbounded one.

## Proof outline

Following Adenwalla (Theorem 1), split `ℤ ∖ {−1, 0}` into levels `X_i = [−8^i, −8^{i−1} − 1] ∪ [8^{i−1}, 8^i − 1]` and order each level first by `x mod 8` (residue order 0,4,2,6,1,5,3,7 on odd levels, reversed on even levels) and then recursively by the position of `⌊x/8⌋` in the previous level; list `{−1, 0}` first and then the levels in increasing order (Adenwalla places `−1` between `X₁` and `X₂`; this reordering removes his Case 3 and is noted in the file). By induction on the level, using finite residue checks mod 8, no level contains a monotone 3-term progression and no 4-term progression has two terms in each of two consecutive levels. Size considerations (Adenwalla's Cases 1 and 2) reduce every monotone 5-term progression to one of these two situations. Positions are realized through the injective key `16^level + rank` and `Nat.Subtype.orderIsoOfNat`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos195.erdos_195.variants.leq_4_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos195.erdos_195.variants.leq_5_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos195.not_hasMonotoneAP_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos195.exists_perm_not_hasMonotoneAP_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos195.le_four_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos195.lean` (`a33bed75289455d4676c31adbe14598ebd825c1c3cf7a0691b44f241ef936641`) are in `verification/`.

## Attribution

- Mathematics: S. Adenwalla, *Avoiding monotone arithmetic progressions in permutations of integers*, arXiv:2211.04451 (2022) [Ad22], Theorem 1; J. Geneson, *Forbidden arithmetic progressions in permutations of subsets of the integers*, Discrete Math. (2019) [Ge19]; both cited by the catalog record JSP-000184 and erdosproblems.com/195. Problem from Erdős–Graham [ErGr79, ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
