# Erdős 261: formal verification for every positive n ≤ 10,000

Submission related to JSP-000226. This package proves the **finite bounded subresult**:

For every integer `1 ≤ n ≤ 10000`, there are at least two distinct positive integers `a₁, …, aₜ` such that

```
n / 2^n = a₁ / 2^a₁ + … + aₜ / 2^aₜ.
```

This is a formalization of a known result, not a solution of the open assertion for all positive integers. It makes no claim about infinite-series representations, award eligibility, prize amount, or first-formalization priority.

## Attribution and related submissions

The bound is due to Szabolcs Tengely, Maciej Ulas, and Jakub Zygadło, *On a Diophantine equation of Erdős and Graham*, Journal of Number Theory 217 (2020), 445–459, Theorem 3.5 ([paper](https://arxiv.org/abs/2008.01501), [DOI](https://doi.org/10.1016/j.jnt.2020.05.006)). Their theorem covers `2 ≤ n ≤ 10000`; the explicit witness `{3,6,8}` supplies `n=1`.

The exact formal statement is adapted from [Formal Conjectures at revision 40e7c98](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/261.lean), with its Apache-2.0 attribution retained in NOTICE. That repository is not imported, and none of its placeholder proofs is trusted.

Prize [PR #60](https://github.com/TheJustinSunPrize/awards/pull/60) treats infinitude and the sharp fixed-term extremum. [PR #85](https://github.com/TheJustinSunPrize/awards/pull/85) treats a counterexample to a separate exponent bound. This package asks for evaluation only of the finite bounded formalization. Prior-art checks are necessarily incomplete; no absolute priority claim is made.

Prepared under GitHub account `James-16` with substantial OpenAI Codex assistance. Mathematical credit remains with the cited authors. Any recipient record should remain `RECIPIENT-JSP-000226-A` until the organizers confirm identity and attribution.

## Proof structure

- `Erdos261Finite.lean`: general semantic proof that a terminating greedy remainder yields a finite set of distinct positive exponents; conversion to the exact `Fin t` statement; proof of the two-term minimum; explicit `n=1` witness.
- `Erdos261Finite/Cert*.lean`: 22,964 short certificate segments covering 2,033,539 shared recurrence states for `n=2,…,10000`. Every segment equality is proved by `rfl`, so Lean's kernel reduces the recurrence itself.
- `Erdos261Finite/FiniteBound.lean`: exhaustive coverage of all 9,999 nontrivial inputs and the final theorem `Erdos261Finite.le_10000`.
- `Erdos261Finite/Audit.lean`: independent restatement of the exact public theorem type and transitive axiom reports.

At a state `(a,r)`, the remaining fraction is `r / 2^a`. The next state is `(a+1, 2r-(a+1))` when `2r ≥ a+1`, adding the exponent `a+1`; otherwise it is `(a+1, 2r)`. The invariant records that every subsequently selected exponent is strictly larger than `a`. Termination yields a finite set; positivity of the tail for `n≥2` proves that adding `n+1` gives at least two terms.

The C++/Python generators are **not trusted proof components**. Incorrect output fails Lean's kernel checks. No `native_decide`, `sorry`, additional axiom, external evaluator, or kernel-check bypass is used in the proof files.

## Reproduction

Install Lean `v4.33.1` using the official Lean toolchain. `lake-manifest.json` pins all dependency commits; mathlib is pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.

From this package directory:

```sh
lake exe cache get Mathlib.Data.Rat.BigOperators Mathlib.Data.Finset.Sort Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.Positivity Mathlib.Tactic.NormNum Mathlib.Tactic.IntervalCases
lake build Erdos261Finite.FiniteBound
lake env lean Erdos261Finite/Audit.lean
```

The cache supplies public dependency build artifacts, not the proofs in this package. The package's source proofs are built locally. To regenerate certificates, run `bash tools/regenerate.sh` (C++17 compiler and Python 3 required), then rebuild. No network, credentials, wallet, or private inputs are used by the generators or proof checker after dependencies are installed.

For the build, axiom audit, and bundled kernel replay together, run `bash tools/verify.sh`. The replay checks the full imported environment and can take longer than the package build. It uses the same Lean implementation, not an independent verifier.

See `verification/RESULTS.md` for recorded checks and their limits.
