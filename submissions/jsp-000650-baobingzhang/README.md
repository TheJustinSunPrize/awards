# JSP-000650: Erdős 791, Mrose's construction disproving g(n) ~ 2√n

Catalog entry: [JSP-000650](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000650) · Problem source: [erdosproblems.com/791](https://www.erdosproblems.com/791)

## Problem

Let `g(n)` be minimal such that there exists `A ⊆ {0, …, n}` of size `g(n)` with `{0, …, n} ⊆ A + A`. Estimate `g(n)`. In particular, is `g(n) ~ 2n^{1/2}`?

## Scope

Partial progress: Mrose's construction, which answers the specific question `g(n) ~ 2√n` negatively and gives `g(n)² ≤ (7/2 + o(1))n`. Estimating `g(n)` precisely remains open; Yu's lower bound and Kohonen's improved upper bound `294/85` are not formalized.

## Formal statements

All results are in `Erdos791.lean`. formal-conjectures has no file for Problem 791; `g` is defined directly from the erdosproblems.com wording as an `sInf` over sizes of `A ⊆ Finset.Icc 0 n` with `Finset.Icc 0 n ⊆ A + A`.

```lean
theorem erdos_791 : ¬ (fun n => (g n : ℝ)) ~[atTop] (fun n => 2 * √(n : ℝ))

theorem not_tendsto_g_div_sqrt : ¬ Tendsto (fun n => (g n : ℝ) / √(n : ℝ)) atTop (𝓝 2)

theorem eventually_g_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (g n : ℝ) ^ 2 ≤ (7 / 2 + ε) * n

theorem mrose_construction (t : ℕ) (ht : 0 < t) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 (14 * t ^ 2 - 1) ∧ #A ≤ 7 * t + 7 ∧
      Finset.Icc 0 (14 * t ^ 2 - 1) ⊆ A + A

theorem g_fourteen_mul_sq_sub_one_le (t : ℕ) (ht : 0 < t) : g (14 * t ^ 2 - 1) ≤ 7 * t + 7

theorem exists_card_eq_g (n : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 n ∧ Finset.Icc 0 n ⊆ A + A ∧ #A = g n
```

For every `t ≥ 1` there is `A ⊆ [0, 14t² − 1]` with `|A| ≤ 7t + 7` and `[0, 14t² − 1] ⊆ A + A`, so `g(14t² − 1) ≤ 7t + 7`. Moreover `g(n)² ≤ (7/2 + ε)n` for all large `n`, hence `g(n)/√n ↛ 2` and `¬ (g ~ 2√n)`. The `sInf` defining `g` is shown to be attained.

## Proof outline

With `V = [0, t]`, `H = {0, t, …, t² − t}`, `S = {0, t+1, …, (t−1)(t+1)}`: `V + H` and `V + S` cover `[0, t² − 1]`, and `(H + S) ∪ (H + S + t²)` covers `[t², 2t² − 1]`. The set `A = (V + t²·{0, 6, 10}) ∪ (H + t²·{0, 1, 2}) ∪ (S + t²·{3})` has `A + A ⊇ [0, 14t² − 1]` by case analysis on the block `⌊n/t²⌋ < 14`. Monotonicity of `g` and `s = ⌊√(n/14)⌋` give the bound for all large `n`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos791.erdos_791' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos791.not_tendsto_g_div_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos791.eventually_g_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos791.mrose_construction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos791.g_fourteen_mul_sq_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos791.exists_card_eq_g' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos791.lean` (`c453daac42c6d2de6125c9e12c5372e793aad4ec198804865ba75ef1d838c0f0`) are in `verification/`.

## Attribution

- Mathematics: A. Mrose, *Untere Schranken für die Reichweiten von Extremalbasen fester Ordnung*, Abh. Math. Sem. Univ. Hamburg 48 (1979), 118–124 [Mr79]; explicit segment form from J. Kohonen, *An improved lower bound for finite additive 2-bases*, J. Number Theory (2017), arXiv:1606.04770, Example 2 [Ko17].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
