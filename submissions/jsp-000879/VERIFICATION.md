# Verification notes for JSP-000879

## Scope of the claim

The formalized claim is the existential statement of JSP-000879:

    ∃ p : ℕ, Nat.Prime p ∧ 2 < p ∧
      ∀ k : ℕ, k! < p → ¬ Nat.Prime (p - k!)

with `AllFactDiffsComposite p` abbreviating the bounded universal. The
witness is `p = 101`, which is also proved to be the least prime `> 2`
with the property (`jsp_000879_least`, via a kernel-checked `decide`
computation over `p ∈ [3, 100]`).

The auxiliary results certify all 56 such primes below `5000`
(`jsp_000879_known_list`, via per-value theorems
`allFactDiffsComposite_<p>`) and record elementary sieve shortcuts
(`factDiffsComposite_auto_two`, `_auto_five`, `_auto_seven`).

Not claimed: whether there are infinitely many such primes — that is the
open question in the source literature (Erdős problem #1059, Guy A2). The
catalog's formulation ("is there a prime…") is existential and is fully
resolved by the witness.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`):
  `jsp_000879`, `jsp_000879_known_list` and `jsp_000879_least` depend only
  on `[propext, Classical.choice, Quot.sound]` — the standard Mathlib
  axioms. No `sorry`, no `native_decide`, no custom axioms. (The `decide`
  used in `exists_prime_diff_below_101` is kernel-reduced and adds no
  axiom.)
- `verify.sh` additionally runs `lake build --wfail` (warnings as
  errors), a prohibited-token scan of the Lean source, and a bundled
  `leanchecker` kernel replay of the produced `.olean`.

## Limitations (honest)

- `leanchecker` is bundled with the same Lean toolchain; it is not an
  independent checker implementation.
- The build uses prebuilt Mathlib oleans fetched by `lake exe cache get`;
  a from-scratch, network-disabled rebuild of Mathlib was not performed.
- The GitHub commit link is pinned but is not a permanent archive such as
  a DOI; no Software Heritage or Zenodo archival is claimed.
- Repository CI validates structure only; it does not check this proof or
  establish mathematical truth.
