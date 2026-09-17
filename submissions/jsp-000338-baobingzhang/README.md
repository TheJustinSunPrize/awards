# JSP-000338: Erdős 411, Steinerberger's reduction and explicit doubling families

Catalog entry: [JSP-000338](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000338) · Problem source: [erdosproblems.com/411](https://www.erdosproblems.com/411)

## Problem

Let `g(n) = n + φ(n)` and `g_k` its `k`-th iterate. Erdős and Graham ask for which `n` and `r` it is true that `g_{k+r}(n) = 2g_k(n)` for all large `k` (they note `n = 10` and `n = 94` with `r = 2`).

## Scope

Partial progress from [St25]: the reduction of the `r = 2` case to `φ(n) + φ(n + φ(n)) = n`, and the explicit infinite families `n = 2^ℓ·m` (`ℓ ≥ 1`, `m ∈ {3, 5, 7, 35, 47}`; `ℓ ≥ 2`, `m = 1`) with `g_{k+2}(n) = 2g_k(n)` for every `k`. Steinerberger's structural restrictions on other solutions and the general classification are not claimed.

## Formal statements

All results are in `Erdos411.lean`. formal-conjectures has no file for Problem 411; `g` is defined directly as `n + φ n` with Mathlib's totient, and `g_k(n)` is `g^[k] n`.

```lean
theorem erdos_411_family {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) (k : ℕ) :
    g^[k + 2] (2 ^ ℓ * m) = 2 * g^[k] (2 ^ ℓ * m)

theorem erdos_411_infinite :
    {n : ℕ | ∀ᶠ k in atTop, g^[k + 2] n = 2 * g^[k] n}.Infinite

theorem g_g_eq_two_mul_iff (m : ℕ) : g (g m) = 2 * m ↔ φ m + φ (m + φ m) = m

theorem totient_add_totient_eq_of {ℓ m : ℕ}
    (h : (1 ≤ ℓ ∧ m ∈ ({3, 5, 7, 35, 47} : Finset ℕ)) ∨ (2 ≤ ℓ ∧ m = 1)) :
    φ (2 ^ ℓ * m) + φ (2 ^ ℓ * m + φ (2 ^ ℓ * m)) = 2 ^ ℓ * m
```

`g(g(m)) = 2m ↔ φ(m) + φ(m + φ(m)) = m` for every `m`; every `n = 2^ℓ·m` in the families above satisfies `g_{k+2}(n) = 2g_k(n)` for all `k ≥ 0` (so it solves `φ(n) + φ(n + φ(n)) = n`); and the set of `n` with `g_{k+2}(n) = 2g_k(n)` for all large `k` is infinite.

## Proof outline

`φ(2^j·c) = 2^j·φ(c)` for even `c`, hence `g(2^j·c) = 2^j·g(c)`. The family `{2^j·c : c ∈ {4, 6, 10, 14, 70, 94}}` is closed under `g` (`g 4 = 6`, `g 6 = 8`, `g 10 = 14`, `g 14 = 20`, `g 70 = 94`, `g 94 = 140`, all by `decide`), and each member satisfies `g(g(n)) = 2n`; induction on `k` gives `g_{k+2}(n) = 2g_k(n)`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos411.erdos_411_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos411.erdos_411_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos411.g_g_eq_two_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos411.totient_add_totient_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos411.lean` (`9c1dffd1ecae93d354418488e93680c5704ff9ae3e287c7653e7c5c3044a8cce`) are in `verification/`.

## Attribution

- Mathematics: S. Steinerberger, *On an iterated arithmetic function problem of Erdős and Graham*, arXiv:2504.08023 (2025) [St25]; the examples `n = 10, 94` are due to Erdős and Graham [ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
