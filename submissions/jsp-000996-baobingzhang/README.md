# JSP-000996: Erdős 1191, Erdős's bound liminf |A∩[1,x]|·(log x)^{1/2}/x^{1/2} < ∞ for infinite Sidon sets

Catalog entry: [JSP-000996](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000996) · Problem source: [erdosproblems.com/1191](https://www.erdosproblems.com/1191)

## Problem

Let `A ⊂ ℕ` be an infinite Sidon set. Is it true that `liminf_{x→∞} |A ∩ [1, x]| / x^{1/2} · (log x)^{1/2} = 0`? Does there exist an infinite Sidon set with `liminf_{x→∞} |A ∩ [1, x]| / x^{1/2} · (log x)^c > 0` for some `c > 0`?

## Scope

Partial progress: Erdős's known upper bound `liminf_{x→∞} |A ∩ [1, x]| / x^{1/2} · (log x)^{1/2} ≤ c` (the result recorded on erdosproblems.com/1191 via [HaRo66]). Both $1000 questions (whether the liminf is 0, and whether some Sidon set has positive liminf with `(log x)^c`) remain open and are not claimed.

## Formal statements

All results are in `Erdos1191.lean`. `IsSidon` is copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Combinatorics/Basic.lean`, Apache-2.0). formal-conjectures has no file for Erdős 1191, so the statement is ours. The same Lean argument is also submitted, as the formal-conjectures variant `erdos_158.variants.isSidon'`, for JSP-000156 (Erdős 158, Sidon special case).

```lean
theorem erdos_1191.variants.erdos_upper_bound {A : Set ℕ} (hAinf : A.Infinite)
    (hAsid : IsSidon A) :
    liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ))) atTop < ⊤

theorem erdos_1191.variants.erdos_upper_bound_explicit {A : Set ℕ} (hAinf : A.Infinite)
    (hAsid : IsSidon A) :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, ((A ∩ Set.Icc 1 x).ncard : ℝ) ≤ C * √(x : ℝ) / √(Real.log x)
```

For every infinite Sidon set `A ⊆ ℕ`: `liminf_{x→∞} ENNReal.ofReal(|A ∩ [1, x]| / x^{1/2} · (log x)^{1/2}) < ⊤` (`erdos_1191.variants.erdos_upper_bound`) and the explicit form `∃ C, ∃ᶠ x in atTop, |A ∩ [1, x]| ≤ C·√x/√(log x)` (`erdos_1191.variants.erdos_upper_bound_explicit`, with `C = 200`). Here `x` ranges over ℕ, which gives an upper bound at least as strong as over real `x`.

## Proof outline

Split `[0, N²)` into `N` blocks of length `N` with counts `F_ℓ`. For a Sidon set, ordered differences of pairs inside the same block are distinct and lie in `(−N, N)`, so `∑ F_ℓ² ≤ 5N`. Cauchy–Schwarz with weights `1/√(ℓ+1)` gives `(∑ F_ℓ/√(ℓ+1))² ≤ 5N(1 + log N)`. If `A(x) > C√(x/log x)` for all large `x`, Abel summation gives `∑ F_ℓ/√(ℓ+1) ≫ C√N (log N − 1)/√(log N)`, and squaring contradicts the previous bound for `C = 100` and large `N`. Hence `A(M)·√(log M) ≤ 100·√M` for arbitrarily large `M`, which gives the finite liminf.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1191.erdos_1191.variants.erdos_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1191.erdos_1191.variants.erdos_upper_bound_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1191.lean` (`99c7288d08f088eb23ca5f5a3bef7fe3ae90611228e249aae57cfc69d1a3773a`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, see H. Halberstam and K. F. Roth, *Sequences*, Vol. I (1966) [HaRo66], and P. Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math. 6 (1980), 89–115 [Er80], as cited by the catalog record JSP-000996 and erdosproblems.com/1191.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
