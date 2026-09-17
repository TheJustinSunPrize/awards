# JSP-000135: Erdős 129 as written is false: Girão's bound R(n;3,r) ≥ c^n for every r ≥ 2

Catalog entry: [JSP-000135](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000135) · Problem source: [erdosproblems.com/129](https://www.erdosproblems.com/129)

## Problem

Let `R(n;k,r)` be the smallest `N` such that if the edges of `K_N` are `r`-coloured then there is a set of `n` vertices which does not contain a copy of `K_k` in at least one of the `r` colours. Prove that there is a constant `C = C(r) > 1` such that `R(n;3,r) < C^{√n}`.

## Scope

Partial progress: the statement of Erdős Problem 129 as written is disproved, following Antonio Girão's observation credited in the catalog record JSP-000135 (the random-colouring bound `R(n;3,r) ≥ c^n`), and the Erdős–Gyárfás lower bound `R(n;3,r) > C^{√n}` is also derived. erdosproblems.com notes that the original source is ambiguous; no claim is made about any other intended formulation (e.g. Erdős's `C_1^{n^{1/(k-1)}} < R(n;k,r) < C_2^{n^{1/(k-1)}}` heuristic).

## Formal statements

All results are in `Erdos129.lean`. formal-conjectures has no file for Erdős 129; the colouring type and `R` are defined in the file following the erdosproblems.com wording ('a set of n vertices which does not contain a copy of K_k in at least one of the r colours', which for `r = k = 2` gives the classical Ramsey numbers). The finite Ramsey theorem used for non-emptiness is proved in the file.

```lean
theorem erdos_129 :
    ¬ ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, (R n 3 r : ℝ) < C ^ Real.sqrt n

theorem erdos_129_disproof (r : ℕ) (hr : 2 ≤ r) :
    ¬ ∃ C : ℝ, 1 < C ∧ ∀ᶠ n : ℕ in atTop, (R n 3 r : ℝ) < C ^ Real.sqrt n

theorem girao_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ n : ℕ in atTop, c ^ n ≤ (R n 3 r : ℝ)

theorem two_pow_lt_R {r n : ℕ} (hr : 2 ≤ r) (hn : 8 * (r ^ 3 - 1) + 12 ≤ n) :
    2 ^ (n / (32 * (r ^ 3 - 1))) < R n 3 r

theorem R_set_nonempty (n k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    {N | ∀ χ : EdgeColouring N r, ∃ S : Finset (Fin N), S.card = n ∧
      ∃ c : Fin r, ∀ T ⊆ S, ¬ (colourClass χ c).IsNClique k T}.Nonempty

theorem erdos_gyarfas_lower_bound (r : ℕ) (hr : 2 ≤ r) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, C ^ Real.sqrt n < (R n 3 r : ℝ)
```

With colourings of the edges of `K_N` (`(⊤ : SimpleGraph (Fin N)).edgeSet → Fin r`) and `R n k r := sInf {N | every colouring has an n-set S and a colour c such that S contains no K_k of colour c}`: `R_set_nonempty` (for `k, r ≥ 2` the set is nonempty, via Ramsey's theorem, so `R` is a genuine minimum), `two_pow_lt_R : 2 ≤ r → 8(r³−1)+12 ≤ n → 2^{⌊n/(32(r³−1))⌋} < R n 3 r`, `girao_lower_bound : ∃ c > 1, ∀ᶠ n, c^n ≤ R n 3 r`, `erdos_129_disproof : 2 ≤ r → ¬ ∃ C > 1, ∀ᶠ n, R n 3 r < C^{√n}`, `erdos_129 : ¬ ∀ r ≥ 2, ∃ C > 1, ∀ n, R n 3 r < C^{√n}`, and `erdos_gyarfas_lower_bound : ∀ C > 1, ∀ᶠ n, C^{√n} < R n 3 r`.

## Proof outline

For an `n`-set `S` listed increasingly and `m = ⌊n/4⌋`, the triangles `{v_i, v_{m+j}, v_{2m+i+j}}` (`i, j < m`) are pairwise edge-disjoint, giving `m²` edge-disjoint triangles. A counting lemma shows that the number of `r`-colourings in which a given colour class has none of these triangles is at most `((r³−1)/r³)^{m²}·r^{|E|}`. A union bound over the `C(N,n)` sets and the `r` colours shows that if `N ≤ 2^{⌊n/(32(r³−1))⌋}` some colouring has, inside every `n`-set, a triangle of every colour, so `R(n;3,r) > N`. Exponential growth then beats every `C^{√n}`. Non-emptiness of the defining set merges colours into `0` and `≠ 0` and applies the finite Ramsey theorem.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos129.erdos_129' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos129.erdos_129_disproof' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos129.girao_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos129.two_pow_lt_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos129.R_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos129.erdos_gyarfas_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos129.lean` (`3e84955cd94864946c8d72b9136f362751b25b57f604c16b6674d2b25dc425f5`) are in `verification/`.

## Attribution

- Mathematics: Antonio Girão (observation on erdosproblems.com/129 that the problem as written is easily disproved, via the random colouring and `≫ n²` edge-disjoint triangles in every `n`-set), credited by the catalog record JSP-000135; P. Erdős and A. Gyárfás, *A variant of the classical Ramsey problem*, Combinatorica 17 (1997) [Er97b] (problem and lower bound `C^{√n}`).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
