# JSP-000945: an integer whose differences from permitted double squares are all prime

## Problem

> Is there an integer whose differences from twice every permitted smaller
> square are all prime?

That is: does there exist a positive integer `n` such that `n - 2 * x^2`
is prime for every `x : ℕ` with `2 * x^2 < n`?

The answer is **yes**. For example `n = 5`: the permitted squares give
`x ∈ {0, 1}`, and `5 - 0 = 5`, `5 - 2 = 3` are both prime.

## What is formalized

`Jsp000945.lean` (Lean 4 + Mathlib) defines

    AllPrimeDiffs n := ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

and proves:

- `jsp_000945` — the formal answer to the problem as stated:

      ∃ n : ℕ, 0 < n ∧ AllPrimeDiffs n

  proved by the explicit witness `n = 5`.

- `jsp_000945_known_list` — certification of the complete known list:
  every `n ∈ {2, 5, 7, 13, 31, 61, 181, 199}` satisfies `AllPrimeDiffs`.
  These are exactly the values recorded in the literature (see Erdős
  problem [#1140](https://www.erdosproblems.com/1140), which asks the
  stronger question of whether *infinitely many* such `n` exist — that
  question remains open and is outside the scope of this formalization,
  as is the conjectured completeness of the list).

- `allPrimeDiffs_prime` — any such `n > 0` is prime (the `x = 0` case).

- `allPrimeDiffs_mod_three` — any such `n > 21` satisfies `n % 3 = 1`:
  for `n > 18` the values `x = 0, 1, 2, 3` are all permitted, and
  `n - 2 ≡ n - 8 ≡ n + 1 (mod 3)` while `n ≡ n - 18 (mod 3)`, so
  `n ≡ 2 (mod 3)` would force `3 ∣ n - 2` with `n - 2 > 3`, and `n ≡ 0`
  would make `n` composite. This is the elementary sieve argument behind
  the observed `n ≡ 1 (mod 3)` pattern in the known list.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000945.lean` | Complete Lean source: definition, lemmas, all theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000945-lean](https://github.com/aznikline/jsp-000945-lean),
pinned commit `7538c6d065a5a7ea0636e649f185f98b54a8e00f`.

## Reproduction

```sh
cd submissions/jsp-000945
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000945-lean.git
cd jsp-000945-lean
git checkout 7538c6d065a5a7ea0636e649f185f98b54a8e00f
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- [EpGi10] M. Epure and A. Gica, "Principal quadratic real fields in
  connection with some additive problems", Bull. Math. Soc. Sci. Math.
  Roumanie (N.S.) 53 (2010), 251–259.
- [MoWi89] R. Mollin and H. Williams, "Period four and real quadratic
  fields of class number one", Proc. Japan Acad. Ser. A Math. Sci. 65
  (1989), 89–93.
