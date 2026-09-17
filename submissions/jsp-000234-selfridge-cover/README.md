# JSP-000234 / Erdős 273: Selfridge's p ≥ 3 covering variant

This package proves the known solved variant allowing primes `p ≥ 3`: a strict covering system exists whose distinct moduli all have the form `p - 1`. The construction uses the prime 3, so **it does not solve the open problem requiring every prime to be at least 5**.

The mathematical existence result is attributed to John Selfridge. The concrete numerical table below comes from a public SAT reconstruction by `idealombrer`. This submission supplies a Lean formalization with an explicit connection to the exact Formal Conjectures structure and target statement.

| Prime p | Modulus p − 1 | Residue |
| --- | --- | --- |
| 3 | 2 | 0 |
| 5 | 4 | 1 |
| 7 | 6 | 1 |
| 11 | 10 | 7 |
| 13 | 12 | 11 |
| 19 | 18 | 9 |
| 31 | 30 | 21 |
| 37 | 36 | 15 |
| 41 | 40 | 3 |
| 61 | 60 | 15 |
| 73 | 72 | 39 |
| 181 | 180 | 39 |

## What is checked

`covers_period` checks all 360 residues using Lean's proof-producing `decide`. Every modulus divides 360, so a proved modular-reduction lemma extends the certificate to every natural number and every integer, including negative integers. This does not rely on running or trusting the SAT search.

`selfridge` constructs `StrictCoveringSystem ℕ` with exactly the original structure fields: a finite index type, coverage by ideal cosets, nonzero proper ideals, and injective moduli. `variants_three` proves each modulus is one less than a prime at least 3. The audit repeats the exact public existential statement and separately checks the all-integer arithmetic interpretation.

The witness also contains a checked example showing that removing its modulus 2 leaves 0 uncovered. This is a scope check for this construction, not a nonexistence proof for the open p ≥ 5 problem.

## Reproduce

Install the toolchain in `lean-toolchain`, then run in this directory:

```sh
lake exe cache get Mathlib.RingTheory.Ideal.Span Mathlib.Data.Nat.Prime.Basic Mathlib.Data.Fin.VecNotation Mathlib.Tactic.NormNum Mathlib.Algebra.Group.Pointwise.Set.Basic Mathlib.Algebra.Module.Submodule.Lattice Mathlib.RingTheory.Ideal.Defs
bash tools/verify.sh
```

The dependency revisions are pinned in `lake-manifest.json`. `leanchecker --fresh` replays the imported environment through the bundled Lean kernel; it is not an independent verifier implementation. See `verification/RESULTS.md` and the accompanying logs and checksums.

## Sources and contribution

- [Erdős Problems 273](https://www.erdosproblems.com/273) and its [recorded history](https://www.erdosproblems.com/history/273) identify Selfridge's construction with divisors of 360.
- [Exact Formal Conjectures variant](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/273.lean).
- [Original structure definitions](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean), copied without changes under Apache-2.0.
- [Pinned numerical certificate](https://github.com/idealombrer/erdos-273-covering-pm1/blob/9d81d4ba5dea78fa66a2fb8ae21212fe5a8a7760/certificates/selfridge_360.out). That repository also contains a Lean parity-reduction proof; its proof code is not used here.

New formalization and packaging: GitHub account `James-16`, with substantial OpenAI Codex assistance. See `NOTICE` for attribution. This is not a new mathematical solution or a claim of exhaustive priority, eligibility, or an award. Committee review is required.
