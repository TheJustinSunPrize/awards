# JSP-000350: Erdős 425, real variant: Alexander's construction of a set A ⊆ [1,x] with |ab − cd| ≥ 1 and |A| ≫ x, refuting |A| = o(x)

Catalog entry: [JSP-000350](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000350) · Problem source: [erdosproblems.com/425](https://www.erdosproblems.com/425)

## Problem

Let `F(n)` be the maximum size of `A ⊆ {1,…,n}` such that the products `ab` (`a < b`) are distinct. Estimate `F(n)`. In the real-number variant: what is the size of the largest `A ⊂ [1,x]` such that for any distinct `a,b,c,d ∈ A` we have `|ab − cd| ≥ 1`? Erdős conjectured `|A| = o(x)`.

## Scope

Partial progress: the real-number variant recorded on erdosproblems.com/425, where Erdős conjectured `|A| = o(x)` and Alexander's construction (reported by Erdős–Graham [ErGr80], given in [Er80]) shows `|A| ≫ x` is possible; this refutes that conjecture. The integer problem (estimating `F(n)`, where Lean formalizations of Erdős's integer bounds exist in Woett/Lean-files, not ours) and the `r`-fold product questions are not formalized or claimed.

## Formal statements

All results are in `Erdos425.lean`. formal-conjectures has no file for Erdős 425; the separation conditions are defined in the file following the erdosproblems.com wording, together with a stronger variant covering all readings of 'distinct'.

```lean
theorem erdos_425_real :
    ∃ c > (0 : ℝ), ∀ᶠ x in atTop, ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧
      c * x ≤ A.card ∧ OneSeparated A ∧ ProductSep A

theorem erdos_425_real_page :
    ∃ c > (0 : ℝ), ∀ᶠ x in atTop, ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧
      c * x ≤ A.card ∧ PairwiseDistinctProductSep A

theorem erdos_425_real_conjecture_false :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ x in atTop, ∀ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x →
      PairwiseDistinctProductSep A → (A.card : ℝ) ≤ ε * x

theorem erdos_425_real_not_isLittleO (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, ∀ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x →
      PairwiseDistinctProductSep A → (A.card : ℝ) ≤ f x) :
    ¬ f =o[atTop] id

theorem exists_large_set (x : ℝ) (hx : 18 ≤ x) :
    ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧ x / 18 ≤ A.card ∧
      OneSeparated A ∧ ProductSep A

theorem alexander_spec {p : ℕ} (hp : p.Prime) :
    (alexander p : Set ℝ) ⊆ Set.Ico (p : ℝ) (9 * p) ∧ (alexander p).card = p ∧
      OneSeparated (alexander p) ∧ ProductSep (alexander p)
```

With `PairwiseDistinctProductSep A` (`|ab − cd| ≥ 1` for pairwise distinct `a,b,c,d ∈ A`, the page's condition), the stronger `ProductSep A` (`|ab − cd| ≥ 1` unless `{a,b} = {c,d}` as multisets) and `OneSeparated A`: `exists_large_set : 18 ≤ x → ∃ A ⊆ [1,x], x/18 ≤ |A| ∧ OneSeparated A ∧ ProductSep A`, `erdos_425_real : ∃ c > 0, ∀ᶠ x, ∃ A ⊆ [1,x], c·x ≤ |A| ∧ OneSeparated A ∧ ProductSep A`, `erdos_425_real_page` (same with the page's condition), `erdos_425_real_conjecture_false : ¬ (∀ ε > 0, ∀ᶠ x, ∀ A ⊆ [1,x], PairwiseDistinctProductSep A → |A| ≤ ε·x)`, and `erdos_425_real_not_isLittleO`.

## Proof outline

Take the Erdős–Turán Sidon set `b_k = 2pk + (k² mod p)`, `k < p` (equal pairwise sums force `{i,j} = {k,l}`), and put `a_k = p·exp(b_k/p²)`. Then `a_i a_j = p²·exp((b_i + b_j)/p²)`, and since distinct pair sums differ by at least 1 and `|e^u − e^v| ≥ |u − v|` for `u, v ≥ 0`, distinct products differ by at least `p²·(1/p²) = 1`; consecutive points are also 1 apart, and `a_k < 9p`. Bertrand's postulate gives a prime `p ∈ (x/18 − 1, x/9]`, producing `p ≥ x/18` points in `[1, x]`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos425.erdos_425_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos425.erdos_425_real_page' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos425.erdos_425_real_conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos425.erdos_425_real_not_isLittleO' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos425.exists_large_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos425.alexander_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos425.lean` (`038fb219d890ca5e25e99b764a2909fe2fb6271abcfbc469c414f8ad05d61019`) are in `verification/`.

## Attribution

- Mathematics: Alexander's construction, reported in P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number theory* (1980) [ErGr80] and given in [Er80], disproving Erdős's conjecture from [Er73], [Er77c]; the simplified exponential form follows the sketch on erdosproblems.com/425; Sidon set of P. Erdős and P. Turán (1941). Cited by the catalog record JSP-000350.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
