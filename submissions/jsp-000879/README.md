# JSP-000879: a prime whose differences from permitted factorials are all composite

## Problem

> Is there a prime whose difference from every permitted smaller factorial
> is composite?

That is: does there exist a prime `p` such that `p - k!` is composite for
every `k : ℕ` with `1 ≤ k! < p`?

The answer is **yes**. For example `p = 101`: the permitted factorials are
`1, 2, 6, 24`, and `101 - 1 = 100`, `101 - 2 = 99`, `101 - 6 = 95`,
`101 - 24 = 77` are all composite.

## What is formalized

`Jsp000879.lean` (Lean 4 + Mathlib) defines

    AllFactDiffsComposite p := ∀ k : ℕ, k! < p → ¬ Nat.Prime (p - k!)

and proves:

- `jsp_000879` — the formal answer to the problem as stated:

      ∃ p : ℕ, Nat.Prime p ∧ 2 < p ∧ AllFactDiffsComposite p

  proved by the explicit witness `p = 101`.

- `jsp_000879_least` — `101` is the least prime `> 2` with the property:
  a kernel-checked `decide` verifies that every prime in `3 ≤ p ≤ 100`
  admits some `k ≤ 4` with `p - k!` prime. (`p = 2` satisfies the literal
  condition trivially since `2 - 1! = 1` is not prime; we treat `p > 2` as
  the meaningful range, matching the source problem's intent.)

- `jsp_000879_known_list` — certification of all 56 primes below `5000`
  satisfying the property: `101, 211, 367, 409, 419, 461, 557, 673, 709,
  769, 937, 967, 1009, 1201, 1259, 1709, 1831, 1889, 2141, 2221, 2309,
  2351, 2411, 2437, 2539, 2647, 2837, 2879, 3011, 3019, 3041, 3049, 3079,
  3163, 3217, 3221, 3359, 3389, 3499, 3593, 3671, 3709, 3833, 3851, 3863,
  3989, 4229, 4271, 4441, 4451, 4691, 4751, 4787, 4861, 4889, 4987`.

- `factDiffsComposite_auto_two` — for every odd prime `p > 3` the `k = 1`
  difference `p - 1` is automatically composite (even and `> 2`).

- `factDiffsComposite_auto_five` — `p ≡ 1 (mod 5)` and `p > 11` makes
  `p - 3! = p - 6` divisible by `5` and `> 5`, hence composite.

- `factDiffsComposite_auto_seven` — `p ≡ 3 (mod 7)` and `p > 31` makes
  `p - 4! = p - 24` divisible by `7` and `> 7`, hence composite.

The stronger source question — whether there are *infinitely many* such
primes (Erdős problem [#1059](https://www.erdosproblems.com/1059), problem
A2 of Guy's collection) — is open and explicitly *not* claimed here.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000879.lean` | Complete Lean source: definition, lemmas, all theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000879-lean](https://github.com/aznikline/jsp-000879-lean),
pinned commit `09bfa27bbdbddafa4688df5df8edbf33d4b22724`.

## Reproduction

```sh
cd submissions/jsp-000879
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000879-lean.git
cd jsp-000879-lean
git checkout 09bfa27bbdbddafa4688df5df8edbf33d4b22724
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- R. K. Guy, *Unsolved Problems in Number Theory*, problem A2.
