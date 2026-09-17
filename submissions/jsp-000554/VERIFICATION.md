# Verification notes for JSP-000554

## Scope of the claim

The catalogue question — "between consecutive primes, is there an
integer whose least prime factor is at least their gap?" — is
formalized with the predicates `ConsecPrimes`, `RoughInGap`,
`Exceptional`. `jsp_000554` proves both sides: an exceptional gap
exists (`(7, 11)`) and a gap containing a rough number exists
(`(3, 5)`, `m = 4`). `jsp_000554_not_forall` states the universal
reading is false.

Auxiliary results: every twin-prime gap contains a rough number; every
cousin-prime gap `(p, p+4)` with `p > 3` is exceptional; gap-6 prime
gaps with `p > 5` are exceptional iff `p % 15 ∈ {1, 8}`; `(7, 11)` is
the least exceptional gap with `p ≥ 3`; `47` is the least start of a
gap `≥ 4` containing a rough number. The two minimality results use
`decide` over decidable reformulations (`GapFree`, `AllSmall`), since
`Nat.minFac` does not kernel-reduce.

Not claimed: the asymptotic theorem of Gafni–Tao
(`N(X) = O(X/log² X)`).

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`): every
  theorem depends only on `[propext, Classical.choice, Quot.sound]` —
  the standard Lean axioms. No `sorry`, no `native_decide`, no custom
  axioms. `decide` calls are kernel-reduced and add no axiom.
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
