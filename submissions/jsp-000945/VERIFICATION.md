# Verification notes for JSP-000945

## Scope of the claim

The formalized claim is the existential statement of JSP-000945:

    ∃ n : ℕ, 0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

with `AllPrimeDiffs n` abbreviating the bounded universal. The witness is
`n = 5`.

The auxiliary results certify every value in the known list
`{2, 5, 7, 13, 31, 61, 181, 199}` (`jsp_000945_known_list`, via per-value
theorems `allPrimeDiffs_*`) and record two structural restrictions:
`allPrimeDiffs_prime` (any such `n > 0` is prime) and
`allPrimeDiffs_mod_three` (any such `n > 21` is `1 mod 3`).

Not claimed: completeness of the known list, or infinitude — the original
source question (Erdős problem #1140) asks whether infinitely many such
`n` exist, which is open. The catalog's formulation ("is there an
integer…") is existential and is fully resolved by the witness.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`):
  `jsp_000945`, `jsp_000945_known_list` and `allPrimeDiffs_mod_three`
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
