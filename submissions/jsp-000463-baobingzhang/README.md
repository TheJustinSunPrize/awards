# JSP-000463: Erdős 573, the Kővári–Sós–Turán–Reiman bound for graphs without C3 and C4

Catalog entry: [JSP-000463](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000463) · Problem source: [erdosproblems.com/573](https://www.erdosproblems.com/573)

## Problem

Is it true that `ex(n; {C₃, C₄}) ∼ (n/2)^{3/2}`? (Erdős–Simonovits.)

## Scope

Partial progress: the classical upper bound cited by the catalog ([KST54]): `ex(n; {C₃, C₄}) ≤ ex(n; C₄) ≤ (n/4)(1 + √(4n − 3)) ≤ n^{3/2}/2 + n/4`. The asymptotic question is open and not claimed; the lower-bound construction is not formalized.

## Formal statements

All results are in `C3C4Free.lean`. "No 4-cycle" is Mathlib's `(cycleGraph 4).Free G`; `cycleGraph_four_isContained_iff` proves it is equivalent to having no four distinct vertices `a ~ b ~ c ~ d ~ a`. `extremalNumber` is Mathlib's definition (also used by formal-conjectures for `ex(n; C_{2k})`); formal-conjectures has no file for Problem 573, so the family version `exC3C4` is defined in the same style.

```lean
theorem exC3C4_le (n : ℕ) : (exC3C4 n : ℝ) ≤ n / 4 * (1 + √(4 * n - 3))

theorem exC3C4_le_rpow (n : ℕ) : (exC3C4 n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + n / 4

theorem extremalNumber_cycleGraph_four_le (n : ℕ) :
    (extremalNumber n (cycleGraph 4) : ℝ) ≤ n / 4 * (1 + √(4 * n - 3))

theorem card_edgeFinset_le_of_free_cycleGraph_four (hG : (cycleGraph 4).Free G) :
    (#G.edgeFinset : ℝ) ≤ Fintype.card V / 4 * (1 + √(4 * Fintype.card V - 3))

theorem cycleGraph_four_isContained_iff :
    cycleGraph 4 ⊑ G ↔ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
```

Every `n`-vertex graph with no 4-cycle has at most `(n/4)(1 + √(4n − 3))` edges. Consequently Mathlib's `extremalNumber n (cycleGraph 4)` and the two-graph extremal number `exC3C4 n` satisfy the same bound, and `exC3C4 n ≤ n^{3/2}/2 + n/4`.

## Proof outline

If distinct `u, w` had two distinct common neighbours `x, y`, then `u–x–w–y–u` would be a 4-cycle, so every pair of distinct vertices has at most one common neighbour. Double counting paths of length two gives `∑ deg(v)² ≤ 2e + n(n − 1)`, and Cauchy–Schwarz gives `(2e)² ≤ n ∑ deg(v)²`. Solving `4e² − 2ne − n²(n − 1) ≤ 0` yields the bound.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'C3C4Free.exC3C4_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3C4Free.exC3C4_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3C4Free.extremalNumber_cycleGraph_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'C3C4Free.card_edgeFinset_le_of_free_cycleGraph_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`C3C4Free.lean` (`1764d7908b839a2e33a92e7ef703510603a719ada129503603bb0d7b90bfef48`) are in `verification/`.

## Attribution

- Mathematics: T. Kővári, V. T. Sós, P. Turán, *On a problem of K. Zarankiewicz*, Colloq. Math. 3 (1954), 50–57 [KST54]; I. Reiman, *Über ein Problem von K. Zarankiewicz*, Acta Math. Acad. Sci. Hungar. 9 (1958), 269–273.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
