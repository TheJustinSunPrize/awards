# Verification notes for JSP-000307

## Scope of the claim

The formalized claim is the existential statement of JSP-000307:

    ∃ n : ℕ, 1 < n ∧
      maxPrimeFac n > maxPrimeFac (n + 1) ∧
      maxPrimeFac (n + 1) > maxPrimeFac (n + 2)

with `maxPrimeFac n := n.primeFactors.sup id`, the largest prime factor of
`n` (`0` for `n < 2`). The witness is `n = 13`.

The auxiliary theorem `jsp_000307_family` (sufficient condition
`p` prime, `p % 6 = 1`, `(p + 1) / 2` prime) strictly generalizes the
decreasing-direction condition of the conditional submission in
`submissions/jsp-000307-conditional` (PR #557): `(p + 2) / 3` need not be
prime. It does *not* establish that infinitely many such `p` exist; that
is an open conditional bound (comparable to Sophie–Germain-type
conjectures) and is not claimed here.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`):
  `jsp_000307` and `jsp_000307_family` depend only on
  `[propext, Classical.choice, Quot.sound]` — the standard Mathlib
  axioms. No `sorry`, no `native_decide`, no custom axioms.
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
