# JSP-000947: an integer whose differences from permitted powers of two are all prime

## Problem

> Is there an integer whose differences from every permitted smaller power
> of two are all prime?

That is: does there exist a positive integer `n` such that `n - 2^k` is
prime for every `k : ℕ` with `1 < 2^k < n`?

The answer is **yes**. For example `n = 7`: the permitted powers are
`2, 4`, and `7 - 2 = 5`, `7 - 4 = 3` are prime.

## What is formalized

`Jsp000947.lean` (Lean 4 + Mathlib) defines

    AllPrimePowDiffs n := ∀ k : ℕ, 1 < 2 ^ k → 2 ^ k < n → Nat.Prime (n - 2 ^ k)

and proves:

- `jsp_000947` — the formal answer to the problem as stated:

      ∃ n : ℕ, 0 < n ∧ AllPrimePowDiffs n

  proved by the explicit witness `n = 7`.

- `jsp_000947_known_list` — certification of the complete known list:
  every `n ∈ {4, 7, 15, 21, 45, 75, 105}` satisfies `AllPrimePowDiffs`.
  These are exactly the values recorded in the literature (see Erdős
  problem [#1142](https://www.erdosproblems.com/1142), OEIS
  [A039669](https://oeis.org/A039669)). The stronger source questions —
  whether any `n > 105` exists, or infinitely many — are open and
  explicitly *not* claimed here; Mientka–Weitzenkamp [MiWe69] verified
  there are no others below `2^44`.

- `allPrimePowDiffs_odd` — any such `n > 4` is odd (since `n - 2` must be
  prime and even).

- `allPrimePowDiffs_three_dvd` — any such `n > 19` is divisible by `3`:
  the permitted differences `n - 2, n - 4, n - 8, n - 16` satisfy
  `n - 2 ≡ n - 8 ≡ n + 1 (mod 3)` and `n - 4 ≡ n - 16 ≡ n - 1 (mod 3)`,
  so `n ≢ 0 (mod 3)` forces a composite difference.

- `allPrimePowDiffs_five_dvd` — any such `n > 21` is divisible by `5`:
  `n - 2, n - 4, n - 8, n - 16` cover all four nonzero residue classes
  mod `5`, so `n ≢ 0 (mod 5)` forces a difference `≡ 0 (mod 5)`
  exceeding `5`.

- `allPrimePowDiffs_fifteen_dvd` — combining the previous two: any such
  `n > 21` is divisible by `15`, matching the observed
  `45, 75, 105 ≡ 0 (mod 15)`.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000947.lean` | Complete Lean source: definition, lemmas, all theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000947-lean](https://github.com/aznikline/jsp-000947-lean),
pinned commit `436e23a5e1bf265aac0ed9ecd33f6d968ab07a9e`.

## Reproduction

```sh
cd submissions/jsp-000947
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000947-lean.git
cd jsp-000947-lean
git checkout 436e23a5e1bf265aac0ed9ecd33f6d968ab07a9e
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- [MiWe69] W. Mientka and R. Weitzenkamp, "On f-plentiful numbers",
  J. Combinatorial Theory 7 (1969), 374–377.
- [Va73] R. Vaughan, "Some applications of Montgomery's sieve",
  J. Number Theory 5 (1973), 64–79.
