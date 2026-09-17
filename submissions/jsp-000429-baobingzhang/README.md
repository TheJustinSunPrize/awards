# JSP-000429: Erdős 535, Erdős's 1964 lower bound f_r(N) > N^{c/log log N} for sets with no r elements of equal pairwise gcd

Catalog entry: [JSP-000429](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000429) · Problem source: [erdosproblems.com/535](https://www.erdosproblems.com/535)

## Problem

Let `r ≥ 3`, and let `f_r(N)` denote the size of the largest subset of `{1,…,N}` such that no subset of size `r` has the same pairwise greatest common divisor between all elements. Estimate `f_r(N)`.

## Scope

Partial progress: Erdős's lower bound [Er64] `f_r(N) > N^{c/log log N}` for every `r ≥ 3` (with one constant `c = 1/16` for all `r`), recorded on erdosproblems.com/535 and credited in the catalog record JSP-000429; this includes the formal-conjectures variant `erdos_535.variants.lower_bound`. The upper bounds (Erdős `N^{3/4+o(1)}`, Abbott–Hanson `N^{1/2+o(1)}`, the sunflower-based `N^{o(1)}`) and Erdős's conjecture that the lower bound is sharp are not formalized or claimed.

## Formal statements

All results are in `Erdos535.lean`. `f` and the statement of `erdos_535.variants.lower_bound` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/535.lean`, Apache-2.0); equivalence with formal-conjectures' opens (so that `log` is `Real.log`) was checked in a scratch file.

```lean
theorem erdos_535.variants.lower_bound : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) ≤ (f 3 N : ℝ)

theorem erdos_535.variants.lower_bound_of_three_le {r : ℕ} (hr : 3 ≤ r) : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) < (f r N : ℝ)

theorem exists_card_eq_f {r : ℕ} (hr : 1 ≤ r) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoEqualGcd r A ∧ A.card = f r N

theorem f_le (r N : ℕ) : f r N ≤ N

theorem f_mono {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (N : ℕ) : f r N ≤ f s N
```

`erdos_535.variants.lower_bound : ∃ c > 0, ∀ᶠ N in atTop, N^{c / log log N} ≤ f 3 N` with formal-conjectures' exact definition of `f` and statement, and `erdos_535.variants.lower_bound_of_three_le : 3 ≤ r → ∃ c > 0, ∀ᶠ N in atTop, N^{c / log log N} < f r N`. `f` is a genuine maximum (`f_le : f r N ≤ N`, `exists_card_eq_f` for `r ≥ 1`), and `f_mono` gives `f 3 N ≤ f r N`.

## Proof outline

Take the first `2m` primes in pairs `{p_{2i}, p_{2i+1}}` and, for `T ⊆ {0,…,m−1}`, let `a_T = ∏_{i<m} p_{2i+[i∈T]}`; these `2^m` numbers are distinct. For three distinct `a_T, a_U, a_V`, at a pair where two choices differ, some prime divides one pairwise gcd but not another, so no three have equal pairwise gcds. All `a_T` divide the primorial of `y` when `2m ≤ π(y)`, which is at most `4^y`. Mathlib's Chebyshev bounds (`Chebyshev.psi_ge`, `psi_le_primeCounting_mul_log`) give `π(y)·log y ≥ y log 2 − log(y+1)`; with `y = ⌊log N/log 4⌋` this yields `2^m > N^{(1/16)/log log N}` for large `N`. Monotonicity in `r` extends the bound to all `r ≥ 3`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos535.erdos_535.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos535.erdos_535.variants.lower_bound_of_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos535.exists_card_eq_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos535.f_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos535.f_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos535.lean` (`bc9a3957ce38cac72ff1ac1f5d1cfec4643faad0c8c44fdc5d6bcc0a1cc22d20`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, *On a problem in elementary number theory and a combinatorial problem*, Math. Comp. 18 (1964) 644–646 [Er64], cited by the catalog record JSP-000429 and erdosproblems.com/535. The block construction is the classical one; its bookkeeping and constants were written during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
