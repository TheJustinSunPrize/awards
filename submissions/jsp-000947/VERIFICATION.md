# Verification notes for JSP-000947

## Scope of the claim

The formalized claim is the existential statement of JSP-000947:

    ∃ n : ℕ, 0 < n ∧ ∀ k : ℕ, 1 < 2 ^ k → 2 ^ k < n → Nat.Prime (n - 2 ^ k)

with `AllPrimePowDiffs n` abbreviating the bounded universal. The witness
is `n = 7`.

The auxiliary results certify every value in the known list
`{4, 7, 15, 21, 45, 75, 105}` (`jsp_000947_known_list`, via per-value
theorems `allPrimePowDiffs_*`) and record elementary sieve restrictions:
any such `n > 4` is odd, any such `n > 19` is divisible by `3`, any such
`n > 21` is divisible by `5`, hence by `15`.

Not claimed: whether any `n > 105` exists, or infinitude — those are the
open questions in the source literature (Erdős problem #1142). The
catalog's formulation ("is there an integer…") is existential and is
fully resolved by the witness.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`):
  `jsp_000947`, `jsp_000947_known_list` and `allPrimePowDiffs_fifteen_dvd`
  depend only on `[propext, Classical.choice, Quot.sound]` — the standard
  Mathlib axioms. No `sorry`, no `native_decide`, no custom axioms.
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
