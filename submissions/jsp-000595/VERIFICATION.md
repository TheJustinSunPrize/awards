# Verification notes for JSP-000595

## Scope of the claim

The formalized claim is the existential statement of JSP-000595:

    ∃ n k : ℕ, 2 ≤ k ∧
      (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)

with `FactSqDivides n k` abbreviating the divisibility. The witness is
`n = 208`, `k = 2`, i.e. `(210)!² ∣ (416)!`, checked by kernel reduction.
Auxiliary results prove `208` is the least `k = 2` witness
(`jsp_000595_least_k2`, via a `decide` computation over Legendre
valuations), certify the further witnesses `k=2: 458, 987`, the least
`k = 3` witness `n = 3475`, and a `k = 4` witness `n = 8174`, and record
the prime-obstruction lemma (a prime in `(n, n+k]` blocks divisibility)
and downward monotonicity in `k`.

Not claimed: whether `(n+k)!² ∣ (2n)!` holds for *infinitely many* `n`
with fixed `k ≥ 2` — that is the open EGRS conjecture (Erdős #727). The
`k = 1` infinitude was settled by Balakran (1929) but is not formalized
here; only the `n = 5` instance is certified.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and Mathlib
  `v4.34.0` (commit `5ed2965256430c3649e86755f9576b54eca72435`).
- `#print axioms` (recorded in `verification/axioms.txt`):
  `jsp_000595` depends only on `[propext]` and `jsp_000595_least_k2` on
  `[propext, Classical.choice, Quot.sound]` — the standard Mathlib axioms.
  No `sorry`, no `native_decide`, no custom axioms. The `decide` calls are
  kernel-reduced and add no axiom.
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
