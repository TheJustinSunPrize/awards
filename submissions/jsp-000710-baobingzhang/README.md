# JSP-000710: Erdős 857, the Naslund–Sawin bound m(n,3) ≤ (3/2^{2/3})^{(1+o(1))n} via slice rank

Catalog entry: [JSP-000710](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000710) · Problem source: [erdosproblems.com/857](https://www.erdosproblems.com/857)

## Problem

Let `m = m(n,k)` be minimal such that in any collection of sets `A_1,…,A_m ⊆ {1,…,n}` there is a sunflower of size `k` (some `k` of the sets pairwise have the same intersection). Estimate `m(n,k)`, or even better, give an asymptotic formula.

## Scope

Partial progress: the case `k = 3`, namely the Naslund–Sawin upper bound (Forum Math. Sigma 2017), credited in the catalog record JSP-000710 and on erdosproblems.com/857: `m(n,3) ≤ 3(n+1)∑_{i≤n/3} C(n,i) + 1` and hence `m(n,3) ≤ (3/2^{2/3})^{(1+o(1))n}`. Lower bounds, the case `k ≥ 4`, and an asymptotic formula are not formalized or claimed.

## Formal statements

All results are in `Erdos857.lean`. `IsSunflowerWithKernel`, `IsSunflower` and `m` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/857.lean` and its sunflower definitions, Apache-2.0); formal-conjectures has only the open main theorem, so the `variants.*` names are ours, following its naming convention. Families consist of distinct sets, as in formal-conjectures and the paper.

```lean
theorem erdos_857.variants.naslund_sawin (n : ℕ) :
    m n 3 ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k + 1

theorem erdos_857.variants.naslund_sawin_rpow (n : ℕ) :
    (m n 3 : ℝ) ≤ 3 * (n + 1) * (3 / 2 ^ (2 / 3 : ℝ)) ^ n + 1

theorem erdos_857.variants.naslund_sawin_asymp :
    ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
      ∀ n ≥ 1, (m n 3 : ℝ) ≤ (3 / 2 ^ (2 / 3 : ℝ)) ^ ((1 + o n) * n)

theorem ncard_le_of_sunflowerFree (n : ℕ) (F : Set (Set (Fin n)))
    (hF : ∀ S ⊆ F, S.ncard = 3 → ¬ IsSunflower S) :
    F.ncard ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k

theorem exists_sunflower_of_lt_ncard (n : ℕ) (F : Set (Set (Fin n)))
    (hF : 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k < F.ncard) :
    ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S

theorem m_three_le_iff (n t : ℕ) :
    m n 3 ≤ t ↔
      ∀ F : Set (Set (Fin n)), t ≤ F.ncard → ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S

theorem m_zero_three : m 0 3 = 2

theorem card_le_of_diagonal {K ι β : Type*} [Field K] [DecidableEq K] [Infinite K] [Fintype ι]
    [DecidableEq ι] (T : ι → ι → ι → K) (hoff : ∀ x y z, T x y z ≠ 0 → x = y ∧ x = z)
    (hdiag : ∀ x, T x x x ≠ 0)
    (s₁ s₂ s₃ : Finset β) (f₁ f₂ f₃ : β → ι → K) (g₁ g₂ g₃ : β → ι → ι → K)
    (hT : ∀ x y z, T x y z = ∑ a ∈ s₁, f₁ a x * g₁ a y z + ∑ b ∈ s₂, f₂ b y * g₂ b x z +
      ∑ c ∈ s₃, f₃ c z * g₃ c x y) :
    Fintype.card ι ≤ #s₁ + #s₂ + #s₃
```

With formal-conjectures' `IsSunflower` and `m` (verbatim): `ncard_le_of_sunflowerFree : (∀ S ⊆ F, S.ncard = 3 → ¬ IsSunflower S) → F.ncard ≤ 3(n+1)∑_{i≤n/3} C(n,i)` (Theorem 3 of the paper), `erdos_857.variants.naslund_sawin : m n 3 ≤ 3(n+1)∑_{i≤n/3} C(n,i) + 1`, `naslund_sawin_rpow : m n 3 ≤ 3(n+1)(3/2^{2/3})^n + 1`, and `naslund_sawin_asymp : ∃ o → 0, ∀ n ≥ 1, m n 3 ≤ (3/2^{2/3})^{(1+o n) n}` (the form on the problem page; `m 0 3 = 2` shows `n ≥ 1` is needed). `m_three_le_iff` shows `m n 3` is the genuine least threshold, and `card_le_of_diagonal` is Tao's slice-rank lemma.

## Proof outline

Split a 3-sunflower-free family by set size into `n+1` layers. Within a layer, the tensor `T(x,y,z) = ∏_i (2 − x_i − y_i − z_i)` over `ℚ` (on indicator vectors) vanishes unless `x = y = z`: three distinct sets of equal size with `T ≠ 0` would form a sunflower with kernel `x ∩ y ∩ z`, and `x = y ≠ z` is impossible for equal sizes. Tao's lemma (a diagonal tensor with nonzero diagonal written as a sum of slices needs at least `|A|` slices, proved via a maximal-support argument) gives the lower bound `|layer|` on the slice rank. Expanding `T` over monomials and grouping each by a variable block of degree `≤ n/3` gives the upper bound `3∑_{i≤n/3} C(n,i)`. Summing over layers and a binomial/entropy estimate `∑_{i≤n/3} C(n,i) ≤ (3/2^{2/3})^n` give the asymptotic form. No slice-rank machinery exists in Mathlib; it was written from scratch.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos857.erdos_857.variants.naslund_sawin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.erdos_857.variants.naslund_sawin_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.erdos_857.variants.naslund_sawin_asymp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.ncard_le_of_sunflowerFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.exists_sunflower_of_lt_ncard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.m_three_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.m_zero_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos857.card_le_of_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos857.lean` (`e6f30f22ef8a6d0af0706ea10f8d29101e8a7b2cb098e7727b07c2d9eddd8aec`) are in `verification/`.

## Attribution

- Mathematics: E. Naslund, W. Sawin, *Upper bounds for sunflower-free sets*, Forum Math. Sigma 5 (2017) e15 [NaSa17] (arXiv:1606.09575), cited by the catalog record JSP-000710 and erdosproblems.com/857; slice-rank method of T. Tao (after Croot–Lev–Pach and Ellenberg–Gijswijt); problem of Erdős [Er70] and Erdős–Szemerédi.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
