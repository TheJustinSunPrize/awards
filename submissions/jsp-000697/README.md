# JSP-000697: square-product completion intervals

## Problem

> How short a following interval supplies larger integers whose
> product with a given integer is a square?

This is Erdős–Graham–Selfridge problem B30 (erdosproblems.com #841).
For a positive integer `n`, let `t_n` be the smallest `t` such that
some subset of `{n+1, …, n+t}` has product with `n` equal to a perfect
square (with `t_n = 0` when `n` is itself a square). The classical
example is `t_6 = 6` via `6·8·12 = 24²`. The asymptotic distribution of
`t_n` was resolved by Bui–Pratt–Zaharescu (2024); this submission
formalizes the *finite, exactly verifiable* content of the problem.

## What is formalized

`Jsp000697.lean` (Lean 4 + Mathlib) defines

    SquareProduct n t := ∃ s ∈ (Finset.Ioc n (n+t)).powerset,
                           IsSquare (n * s.prod id)

and proves:

- `squareProduct_mono` — enlarging the interval preserves witnesses.
- `squareProduct_zero_of_isSquare` / `isLeast_squareProduct_zero` —
  `t_n = 0` for square `n` (empty subset).
- `not_squareProduct_of_odd_factorization` — the general obstruction:
  if a prime `p` divides `n` to an odd power then `t_n ≥ p`, since no
  element of `(n, n+t]` with `t < p` is divisible by `p`.
- `squareProduct_prime_lower` — `t_p ≥ p` for every prime `p`.
- `squareProduct_prime_upper` — if `k² < p < 2k²` then
  `{2k², 2p} ⊆ (p, 2p]` gives `t_p ≤ p` (`p·2k²·2p = (2pk)²`).
- `jsp_000697_prime` — **`t_p = p` for every prime sandwiched in
  `(k², 2k²)`**, instantiated for all 23 primes `5 ≤ p ≤ 97`
  (`isLeast_squareProduct_{5,…,97}`).
- `jsp_000697` — the canonical example **`t_6 = 6`** (`IsLeast`),
  certified by exhaustive kernel enumeration of all 32 sublists of
  `{7,…,11}`.
- `isLeast_squareProduct_*` — exact certified values `IsLeast` of `t_n`
  for every non-square `n ≤ 27` and for `n ∈ {33, 34, 38, 39, 40}`,
  either by exhaustive sublist enumeration (`isLeast_of_witness`) or by
  the obstruction bound being attained (`isLeast_of_prime_factor`, for
  `n = 14, 21, 22, 26, 33, 34, 38, 39`).
- `squareProduct_{28,30,32,35}_{lower,upper}` — explicit bounds where
  the exhaustive check would enumerate ≥ 2048 sublists:
  `7 ≤ t_28 ≤ 12`, `5 ≤ t_30 ≤ 12`, `2 ≤ t_32 ≤ 13`, `7 ≤ t_35 ≤ 13`.

Not claimed: the asymptotic theorem of Bui–Pratt–Zaharescu.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000697.lean` | Complete Lean source: definitions, lemmas, theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000697-lean](https://github.com/aznikline/jsp-000697-lean),
pinned commit `54383d1257a1d3ed0a6b81868a3265246e1fb0ab`.

## Reproduction

```sh
cd submissions/jsp-000697
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000697-lean.git
cd jsp-000697-lean
git checkout 54383d1257a1d3ed0a6b81868a3265246e1fb0ab
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

Note: the exhaustive sublist checks make the build CPU-heavy
(≈ 4 minutes on an Apple-silicon laptop).

## References

- P. Erdős, R. L. Graham, J. L. Selfridge, problem B30 in
  R. K. Guy, *Unsolved Problems in Number Theory*.
- T. Bui, K. Pratt, A. Zaharescu, *Power-saving polynomials and
  the least common multiple of polynomial sequences*, Proc. Cambridge
  Philos. Soc. (2024), doi:10.1017/S0305004123000488.
- erdosproblems.com #841.
