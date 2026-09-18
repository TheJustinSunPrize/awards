# Verification record — all-order supplement, 2026-09-17 UTC

## Tested revision and result

Proof commit: `91a57fa9ab5d0f0f1df3f94e156e29fc4a8ca0f2`.

[Successful public CI run 35177883810](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177883810).
Job: `105063508812`. Every verification step completed successfully.

- Lean 4.34.0 compilation with warnings as errors: successful (3,249 jobs,
  including cached dependencies).
- Bundled `leanchecker AllOrders` replay: successful.
- All eighteen selected axiom audits: successful; each uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- All nine dependency revision checks: successful.
- False-arithmetic negative control: rejected as required.
- Python incidence checks: primes 2,3,5,7,11 passed; the composite-modulus
  negative control at modulus 4 exhibits a 4-cycle as expected. These finite
  checks supplement the original construction; the all-order theorem is
  established by the general Lean proof, not by finite sampling.
- Independently implemented NaNoda checker: **32,138 declarations checked with
  no errors**, under the strict three-axiom allowlist.

The exported targets include the original finite-field construction and lower
bounds, and the new monotonicity, all-order graph-existence and all-order
extremal lower-bound theorems, with their complete dependency closures.

Exporter pin: `6cea97789dc088ea47fcea15692db85685aedac5` in
[leanprover/lean4export](https://github.com/leanprover/lean4export).
Checker pin: `4c544ed4099c8227f07d5de77ad1e69fb0740a27` in
[ammkrn/nanoda_lib](https://github.com/ammkrn/nanoda_lib).

`evidence/all-orders-public-ci-excerpt.log` selects lines from the actual
public job log; it is not the complete log. The run and artifact contain the
larger record. `evidence/all-orders-local-frontend-audit.log` records successful
local development checks, not independently administered verification.

## Artifact and source integrity

[GitHub Actions artifact 10479636775](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177883810/artifacts/10479636775)

- Size: 30,571,637 bytes.
- GitHub-reported ZIP SHA-256:
  `d332f1484bdc3a254c51f84548c8677e789917da435f8b3023d8cd3b3cd01494`.
- Advertised expiry: 2026-12-16T03:21:52Z.
- The ZIP was not downloaded and independently rehashed locally; the metadata
  is reported by GitHub in `evidence/all-orders-artifact-metadata.json`.

AllOrders.lean SHA-256:
`abf342024bf5761cd338c03bf5f9ae8fa6c58001de441fa8604f406e35c02ebd`.

The original JSP000463.lean is unchanged, with SHA-256:
`9cd53bd33d38f5799543102cd64407e81758e5309ac943af7c054dea90d8a197`.

## Submission checks and earlier evidence

All 22 official repository unit tests passed. Repository validation results
are recorded in `evidence/all-orders-preflight.log` against official baseline
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
The submitted Lean sources, lockfile, compiler pin and verification scripts
match the tested proof package. Changes stay within this submission directory.

[VERIFICATION-v1.md](VERIFICATION-v1.md) preserves the original construction's
successful run 35176522636 and 7,703-declaration independent check. The original
artifact-metadata.json, public-ci-excerpt.log, local-frontend-audit.log and
preflight.log refer to that earlier revision, not the all-order supplement.
The original proof and submission commits remain in Git history.

## Scope and limitations

The new conclusion is `n³ < 512 exC3C4(n)²` for every n ≥ 8, together with an
actual graph-existence statement. It is a classical uniform lower bound with
a constant eight times smaller than the conjectured sharp constant. This
submission does not prove the original asymptotic equivalence or a matching
upper bound and does not claim a new mathematical discovery.

Checks were run by the contributor, not an organizer-designated verifier.
The independent implementation refers to NaNoda, not independent human review.
Dependency caches and network access were used; a full offline rebuild of all
foundational dependencies is not claimed. Local checks used a Lean frontend
through Lake; the public run provides the standard build and replay evidence.

Organizer review, scope and priority adjudication, recipient confirmation and
independently administered permanent archival remain pending. No award or
payment entitlement is asserted.
