# JSP-000310: Grimm's conjecture, certified for all intervals in [2, 10⁴]

## Problem

> If `n + 1, …, n + k` are all composite, must there exist distinct
> primes `p₁, …, p_k` with `p_i ∣ n + i`?

This is Grimm's conjecture — Erdős Problem
[#375](https://www.erdosproblems.com/375), Guy B32. The conjecture is
**open** in general: it implies a sub-√x bound on prime gaps and hence
Legendre's conjecture. It was verified computationally by
Laishram–Shorey for `n ≤ 1.9 × 10¹⁰`; this submission formalizes the
finite, kernel-checkable content of the problem plus the unconditional
length-2 case.

## What is formalized

`Jsp000310.lean` (Lean 4 + Mathlib) defines

    GrimmHolds a b := ∃ ps : List ℕ,
      ps.length = b + 1 - a ∧ ValidAssign a ps
    ValidAssign a ps := ps.Nodup ∧
      ∀ i : Fin ps.length, (ps[i]).Prime ∧ ps[i] ∣ a + i

and proves:

- `grimm_certified` — **for every interval `[a, b] ⊆ [2, CERT_N]`**
  (`CERT_N = 10⁴`) whose members are all composite, `GrimmHolds a b`
  holds: there is a list of distinct primes with `ps[i] ∣ a + i`.
- `grimm_certified_len2` — the `[a, a+1]` specialization.
- `grimm_two` — the **unconditional** length-2 case: two consecutive
  composites `m, m+1` always admit distinct prime divisors, since
  `gcd(m, m+1) = 1` (any prime divisors of `m` resp. `m+1` must differ).
- `cert_complete` — every composite in `[2, CERT_N]` lies inside one of
  the certified runs (coverage theorem).
- `cert_valid` — every certificate entry is a valid maximal composite
  run with a valid assignment (`RunOk`).

## Certificate design

`cert` lists all **1228 maximal composite runs** in `[2, 10⁴]`
(maximal run length 35), each equipped with an explicit
distinct-prime assignment (8,771 primes total). Two `decide`-checked
Booleans verify the certificate by kernel reduction:

- `certAllOk`: for every entry `(lo, hi, ps)`, the interior is
  composite, `lo - 1` is prime or `lo ≤ 2`, `hi + 1` is prime or the
  run reaches `CERT_N`, `ps.length = hi - lo + 1`, `ps` is nodup, and
  every `ps[i]` is a prime divisor of `lo + i`.
- `coverOk`: a linear scan of `[2, CERT_N]` showing every non-prime
  position is consumed by some certificate run.

`grimm_certified` then finds the run containing `a`, shows it extends
at least to `b` (otherwise `hi + 1` would be a prime inside `[a, b]`,
or `hi ≥ CERT_N ≥ b`), and restricts the run's assignment by
`List.drop`/`List.take`, which preserves `Nodup`, primality and
divisibility.

All primality tests inside the certificate go through `isPrimeB`, a
fuel-bounded trial-division Boolean (O(√n) kernel reduction) proved
equivalent to `Nat.Prime` via `Nat.prime_def_le_sqrt`; kernel
reduction of `decide (Nat.Prime n)` is linear in `n` and too slow for
the ~28k checks required.

## Scope and limitations

- The full conjecture (all `n`, all `k`) is **open and not claimed**.
  This is a finite certification at `CERT_N = 10⁴` plus the
  unconditional `k ≤ 2` case.
- The bound is a kernel-computation tradeoff, not a restriction of the
  method; the same certificate scheme scales further at more compute.

## Reproduce

```sh
lake build            # ≈ 3.5 min; certificate checks via kernel decide
lake build --wfail
bash verify.sh        # build + warnings-as-errors + token scan + leanchecker
```

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (pinned in
`lakefile.toml` / `lake-manifest.json`).

## Pinned proof repository

- <https://github.com/aznikline/jsp-000310-lean>
- Commit: `fc986e4920ed51e66ac916f4106988f5ba07b14b`
