# JSP-000595: a factorial square dividing a double factorial

## Problem

> Can the square of a factorial with index slightly above a reference
> value divide the factorial of twice that reference value?

i.e. do there exist `n` and `k ≥ 1` with `(n + k)!² ∣ (2n)!`?

The answer is **yes** — in fact already for `k = 2`, e.g.
`(210)!² ∣ (416)!` (`n = 208`). This is the Erdős–Graham–Ruzsa–Straus
question ([EGRS75]; Erdős problem
[#727](https://www.erdosproblems.com/727)). Balakran (1929) showed
`k = 1` holds for infinitely many `n`; infinitude is open for `k ≥ 2`.

## What is formalized

`Jsp000595.lean` (Lean 4 + Mathlib) defines

    FactSqDivides n k := (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)

and proves:

- `jsp_000595` — the formal answer to the problem as stated:

      ∃ n k : ℕ, 2 ≤ k ∧ FactSqDivides n k

  with witness `n = 208`, `k = 2`, verified by kernel reduction of the
  literal divisibility `(210)!² ∣ (416)!`.

- `jsp_000595_least_k2` — `208` is the least `k = 2` witness: every
  `2 ≤ n ≤ 207` fails, since for each such `n` some prime `p ≤ 2n` has
  `2 · v_p((n+2)!) > v_p((2n)!)` (Legendre valuations; kernel-checked
  `decide` over all `n` in range and all primes `≤ 416`).

- `factSqDivides_5_1` — the classical `k = 1` case (`n = 5`, quotient `7`).
- `factSqDivides_458_2`, `factSqDivides_987_2` — further `k = 2` witnesses.
- `factSqDivides_3475_3` — least `k = 3` witness, `(3478)!² ∣ (6950)!`.
- `factSqDivides_8174_4` — a `k = 4` witness, `(8178)!² ∣ (16348)!`.
- `FactSqDivides.mono` — a witness at offset `l` certifies all `k ≤ l`.
- `not_factSqDivides_of_prime_between` — elementary obstruction: a prime
  `p ∈ (n, n+k]` with `k ≤ n` gives `v_p((n+k)!) = v_p((2n)!) = 1`, so the
  square cannot divide. This explains why witnesses are sparse.

The open conjecture — `(n+k)!² ∣ (2n)!` for infinitely many `n`, for any
fixed `k ≥ 2` — is explicitly *not* claimed.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000595.lean` | Complete Lean source: definition, lemmas, all theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000595-lean](https://github.com/aznikline/jsp-000595-lean),
pinned commit `1e1d9a1adb49172b60713c0d99df538201e7b04c`.

## Reproduction

```sh
cd submissions/jsp-000595
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000595-lean.git
cd jsp-000595-lean
git checkout 1e1d9a1adb49172b60713c0d99df538201e7b04c
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- Erdős, Graham, Ruzsa, Straus, *On the prime factors of `C(2n,n)`*,
  Math. Comp. 29 (1975), 83–92.
- H. Balakran, *On the values of `n` which make `(2n)!/(n+1)!(n+1)!` an
  integer*, J. Indian Math. Soc. (1929), 97–100.
- Erdős problem #727, https://www.erdosproblems.com/727.
