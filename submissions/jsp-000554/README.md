# JSP-000554: rough numbers between consecutive primes

## Problem

> Between consecutive primes, is there an integer whose least prime
> factor is at least their gap?

This is a question of Erdős on "rough" numbers inside prime gaps.
Gafni and Tao (arXiv:2508.06463) proved that almost all gaps
`(p_n, p_{n+1})` contain an `m` with `minFac m ≥ p_{n+1} − p_n`, and
bound the count of exceptional gaps by `O(X / log² X)`. The literal
yes/no question is two-sided: exceptional gaps exist *and* gaps
containing rough numbers exist.

## What is formalized

`Jsp000554.lean` (Lean 4 + Mathlib) defines

    ConsecPrimes p q := p.Prime ∧ q.Prime ∧ p < q ∧
                        ∀ r, r.Prime → p < r → q ≤ r
    RoughInGap  p q m := p < m ∧ m < q ∧ q - p ≤ m.minFac
    Exceptional p q := ConsecPrimes p q ∧
                        ∀ m, p < m → m < q → m.minFac < q - p

and proves:

- `jsp_000554` — `∃ p q, Exceptional p q` (witness `(7, 11)`) **and**
  `∃ p q m, ConsecPrimes p q ∧ RoughInGap p q m` (witness `(3, 5)`,
  `m = 4` with `minFac 4 = 2 = gap`).
- `jsp_000554_not_forall` — the universal reading is false.
- `twin_gap_rough` — every twin-prime gap `(p, p+2)`, `p ≥ 3`, contains
  the rough number `p + 1` (even, `minFac = 2 =` gap).
- `cousin_gap_exceptional` — every cousin-prime gap `(p, p+4)`, `p > 3`,
  is exceptional (`p+1, p+3` even; `3 ∣ p+2` since `p+4` prime forces
  `p ≡ 1 mod 3`).
- `sexy_gap_iff` — full mod-15 characterization: a gap-6 prime gap with
  `p > 5` is exceptional iff `p % 15 ∈ {1, 8}`.
- `jsp_000554_least_exceptional` — `(7, 11)` is the least exceptional
  gap with `p ≥ 3` (kernel `decide` over a decidable reformulation).
- `jsp_000554_first_rough_gap` — `47` is the least prime starting a gap
  of length `≥ 4` that contains a rough number (`49 = 7²` in `(47, 53)`;
  kernel `decide` over all prime gaps below `47`).
- Certified instances: `exceptional_7_11`, `exceptional_13_17`,
  `exceptional_23_29`, `exceptional_31_37`, `rough_3_5_4`,
  `rough_5_7_6`, `rough_47_53_49`.

Not claimed: the Gafni–Tao asymptotic theorem itself.

## Files

| File | Role |
| ---- | ---- |
| `Jsp000554.lean` | Complete Lean source: definitions, lemmas, theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000554-lean](https://github.com/aznikline/jsp-000554-lean),
pinned commit `7267199304c4430235de4947634900e8355ba1d4`.

## Reproduction

```sh
cd submissions/jsp-000554
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000554-lean.git
cd jsp-000554-lean
git checkout 7267199304c4430235de4947634900e8355ba1d4
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- A. Gafni, T. Tao, *Rough numbers between consecutive primes*,
  arXiv:2508.06463 (2025).
