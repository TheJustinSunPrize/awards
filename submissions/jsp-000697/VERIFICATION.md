# Verification notes for JSP-000697

## Scope of the claim

The catalogue question — "how short a following interval supplies
larger integers whose product with a given integer is a square?" — is
formalized by `SquareProduct n t`, the least such `t` being `t_n`
(with `t_n = 0` for square `n`, matching the standard convention via
the empty subset).

Proved content:

- The general obstruction `not_squareProduct_of_odd_factorization`:
  a prime `p` dividing `n` to an odd power forces `t_n ≥ p`, proved via
  `Nat.factorization` and `Nat.isSquare_iff_even_factorization`.
- `squareProduct_prime_lower`/`squareProduct_prime_upper`: `t_p = p`
  whenever `k² < p < 2k²` (witness `{2k², 2p}`), giving
  `jsp_000697_prime` and 23 instantiations for `5 ≤ p ≤ 97`.
- `jsp_000697`: the classical `t_6 = 6`, an `IsLeast` statement whose
  lower-bound half is certified by enumerating all 32 sublists of
  `{7,…,11}` in the kernel.
- Exact `IsLeast` values of `t_n` for all non-square `n ≤ 27` and for
  `n ∈ {33, 34, 38, 39, 40}` (`isLeast_of_witness` enumeration, or
  `isLeast_of_prime_factor` when the obstruction bound is attained).
- Bounds-only results for `n ∈ {28, 30, 32, 35}`, where exhaustive
  enumeration would exceed ~2000 sublists.

Not claimed: the asymptotic theorem of Bui–Pratt–Zaharescu (2024), and
exact values `t_28, t_30, t_32, t_35` (upper and lower bounds are given
instead, so the statements remain fully proved).

## Kernel-reduction notes

`Nat.sqrt` does not reduce in the Lean kernel (well-founded recursion),
so squareness inside `decide` checks is tested by `binSqrt`, a
fuel-bounded binary-search root whose specification is proved in
`binSqrtLoop_spec`/`isSquare_iff_binSqrt`. `Finset.powerset` membership
checks are avoided in the exhaustive step: subsets are enumerated as
`List.sublists` of `List.range'`, and `exists_sublist_prod` proves
every `Finset` subset of `Ioc n (n+u)` is realized by such a sublist
with the same product (via `Subperm`). `Nat.factorization` likewise
does not kernel-reduce, so odd-exponent hypotheses are discharged
through `factorization_eq_one_of_sqfree` and
`Nat.factorization_pow_self`, never by evaluation.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
  Build time ≈ 4 minutes, dominated by the kernel enumeration.
- `#print axioms` (recorded in `verification/axioms.txt`): `jsp_000697`,
  `jsp_000697_prime` and `isLeast_squareProduct_40` depend only on
  `[propext, Classical.choice, Quot.sound]` — the standard Lean axioms.
  No `sorry`, no `native_decide`, no custom axioms.
- `verify.sh` additionally runs `lake build --wfail` (warnings as
  errors), a prohibited-token scan of the Lean source, and a bundled
  `leanchecker` kernel replay of the produced `.olean`.

## Limitations (honest)

- `leanchecker` is bundled with the same Lean toolchain; it is not an
  independent checker implementation.
- The build uses prebuilt Mathlib oleans fetched by
  `lake exe cache get`; a from-scratch, network-disabled rebuild of
  Mathlib was not performed.
- The GitHub commit link is pinned but is not a permanent archive such
  as a DOI; no Software Heritage or Zenodo archival is claimed.
- Repository CI validates structure only; it does not check this proof
  or establish mathematical truth.
- An existing contribution for this problem (issue/PR #445) formalizes
  the original density-zero statement; this submission is complementary
  finite content (exact values, obstruction theorem, prime family) and
  does not duplicate that statement-level work.
