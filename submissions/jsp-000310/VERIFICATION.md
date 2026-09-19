# Verification notes for JSP-000310

## Scope of the claim

The catalogue problem is Grimm's conjecture (Erdős Problem #375, Guy
B32): for every run `n + 1, …, n + k` of consecutive composites there
exist distinct primes `p_i` with `p_i ∣ n + i`.

Proved content:

- `grimm_certified`: the conjecture holds for **every** composite
  interval `[a, b] ⊆ [2, CERT_N]` with `CERT_N = 10⁴`, certified by an
  explicit list of all 1228 maximal composite runs in `[2, 10⁴]`
  together with distinct-prime assignments (8,771 primes).
- `cert_complete`: every composite in `[2, CERT_N]` is covered by a
  certificate run.
- `cert_valid`: every certificate entry is a genuine maximal run with
  a valid assignment.
- `grimm_two`: the unconditional length-2 case (`gcd(m, m+1) = 1`),
  recorded as trivial on the problem page.

Not claimed: the full conjecture for unbounded `n`, which remains open
(it would imply a sub-√x bound on prime gaps). Laishram–Shorey verified
it computationally to `1.9 × 10¹⁰`; this submission contributes a
*kernel-checked* certification, not a new record.

## Kernel-reduction notes

`decide (Nat.Prime n)` reduces linearly in `n` inside the kernel, which
is too slow for the ~28k primality tests the certificate requires. All
such tests instead go through `isPrimeB`, a fuel-bounded structural
trial division up to `√n`, bridged to `Nat.Prime` by
`trialAux_true`/`trialAux_false` and `Nat.prime_def_le_sqrt`. Composite
interiors are enumerated by `List.range'` rather than `Finset.Icc`
membership, avoiding kernel construction of nodup witnesses. Coverage
is a single linear `coverOk` scan whose fuel accounts for both scanned
positions and popped certificate intervals.

## Local verification performed

- `lake build`: all theorems type-check under Lean `4.34.0` and
  Mathlib `v4.34.0`. Build time ≈ 3.5 minutes, dominated by the
  `certAllOk`/`coverOk` kernel evaluations.
- `lake build --wfail`: clean, no warnings.
- `lean -DwarningAsError=true Jsp000310.lean`: clean.
- `#print axioms` (recorded in `verification/axioms.txt`):
  `grimm_certified` and `grimm_two` depend only on
  `[propext, Classical.choice, Quot.sound]` — the standard Lean axioms.
  No `sorry`, no `native_decide`, no custom axioms.
- `verify.sh` additionally runs a prohibited-token scan of the Lean
  source and a bundled `leanchecker` kernel replay of the `.olean`.

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
- No existing PR for JSP-000310 was found at submission time.
