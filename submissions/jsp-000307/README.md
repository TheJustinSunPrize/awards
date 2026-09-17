# JSP-000307: decreasing largest prime factors of three consecutive integers

## Problem

> Can three consecutive integers have strictly decreasing largest prime
> factors?

Write `P(n)` for the largest prime factor of `n`. The answer is **yes**:
the smallest witness is `n = 13`, since

    P(13) = 13 > P(14) = 7 > P(15) = 5.

## What is formalized

`Jsp000307.lean` (Lean 4 + Mathlib) defines

    maxPrimeFac n := n.primeFactors.sup id

(the largest element of the finset of prime factors; `0` for `n < 2`) and
proves:

- `jsp_000307` — the formal answer to the problem as stated:

      ∃ n : ℕ, 1 < n ∧
        maxPrimeFac n > maxPrimeFac (n + 1) ∧
        maxPrimeFac (n + 1) > maxPrimeFac (n + 2)

  proved by the explicit witness `n = 13`. This resolves the existential
  question only; the theorem that *infinitely many* such triples exist
  (Erdős–Pomerance [ErPo78], Balasubramanian [Ba01]) is outside the scope
  of this formalization.

- `jsp_000307_family` — a sufficient condition for decreasing triples:
  for every prime `p` with `p % 6 = 1` such that `(p + 1) / 2` is prime,

      maxPrimeFac p = p  >  maxPrimeFac (p + 1) = (p + 1) / 2
                          >  maxPrimeFac (p + 2) ≤ (p + 2) / 3.

  Unlike the sufficient condition in submission
  `submissions/jsp-000307-conditional` (PR #557), which additionally
  requires `(p + 2) / 3` to be prime, this condition needs only
  `3 ∣ p + 2` and `p + 2` odd (both automatic from `p % 6 = 1`), because
  every prime factor `q` of an odd composite `3 ∣ n` satisfies
  `q ≤ n / 3` (lemma `maxPrimeFac_le_third`). For example `p = 277`
  yields `277 > 139 > 31` while `(p + 2) / 3 = 93` is composite — a case
  not covered by the stronger condition (`jsp_000307_family_277`).

## Files

| File | Role |
| ---- | ---- |
| `Jsp000307.lean` | Complete Lean source: definition, lemmas, all theorems. |
| `lakefile.toml` / `lake-manifest.json` | Pinned Mathlib `v4.34.0` dependency. |
| `lean-toolchain` | Pinned Lean `4.34.0`. |
| `verify.sh` | Reproduction script (build, warnings-as-errors, prohibited-token scan, bundled `leanchecker` replay). |
| `verification/` | Recorded toolchain versions, axiom report, source checksums. |
| `.gitignore` | Ignores the local `.lake` build cache. |

## Immutable proof source

Public proof repository:
[aznikline/jsp-000307-lean](https://github.com/aznikline/jsp-000307-lean),
pinned commit `9c27196f72c2359226ceb020244ebf6278be6a75`.

## Reproduction

```sh
cd submissions/jsp-000307
lake exe cache get   # requires network
bash verify.sh
```

or, from the pinned proof repository,

```sh
git clone https://github.com/aznikline/jsp-000307-lean.git
cd jsp-000307-lean
git checkout 9c27196f72c2359226ceb020244ebf6278be6a75
lake exe cache get
lake build
```

Requires elan. Lean is pinned to `4.34.0`, Mathlib to `v4.34.0`
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## References

- [ErPo78] P. Erdős and C. Pomerance, "On the largest prime factors of n
  and n+1", Aequationes Math. 17 (1978), 311–321.
- [Ba01] R. Balasubramanian, "On triplets with descending largest prime
  factors", Studia Sci. Math. Hungar. 36 (2001), 45–50.
