# Verification record — 2026-09-17 UTC

## Tested revision and result

Proof commit: `91cc5632694304c3a9764cd676088cafb573a799`.

[Successful public CI run 35176522636](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176522636).
Job: `105059337292`. All verification steps completed successfully.

- Lean 4.34.0 compilation with warnings as errors: successful (3,127 jobs,
  including cached dependencies).
- Bundled `leanchecker JSP000463` replay: successful.
- All eleven selected axiom audits: successful; each uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- All nine dependency revision checks: successful.
- False-arithmetic negative control: rejected as required.
- Python incidence checks: primes 2,3,5,7,11 passed. Modulus 4 has a 4-cycle,
  as required for the composite-modulus negative control.
- Independently implemented NaNoda checker: **7,703 declarations checked with
  no errors**, under a strict three-axiom allowlist.

Exporter pin: `6cea97789dc088ea47fcea15692db85685aedac5` in
[leanprover/lean4export](https://github.com/leanprover/lean4export).
Checker pin: `4c544ed4099c8227f07d5de77ad1e69fb0740a27` in
[ammkrn/nanoda_lib](https://github.com/ammkrn/nanoda_lib).

`evidence/public-ci-excerpt.log` is a selection of the actual timestamped public
job log, not the complete log. The run and artifact preserve the larger record.
`evidence/local-frontend-audit.log` records earlier local development checks,
not a separate independently administered verification.

## Artifact

[GitHub Actions artifact 10478881733](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176522636/artifacts/10478881733)

- Size: 4,642,937 bytes.
- GitHub-reported ZIP SHA-256:
  `490ab6f4a4b8573777e4cd623d677912c68ac6855391e5a0e2759045e0ff9fe6`.
- Advertised expiry: 2026-12-16T03:00:20Z.
- The ZIP was not downloaded and independently rehashed locally; the metadata
  is reported by GitHub, as recorded in `evidence/artifact-metadata.json`.

Lean source SHA-256:
`9cd53bd33d38f5799543102cd64407e81758e5309ac943af7c054dea90d8a197`.

## Submission checks

All 22 official repository unit tests passed. The unmodified organizer scripts
passed `validate`, `links`, `build`, `check`, and `history` against
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
The submitted source, manifest, compiler pin and verification scripts match
the tested proof package. Only docs/submissions/jsp-000463-kz is added.

The earlier proof run 35176347605 compiled and replayed the same Lean source,
but its audit invocation used an unsupported `lean --wfail` option. The next
commit changed that script to `lean -DwarningAsError=true`; the complete rerun
listed above passed. The failed attempt is not counted as successful verification.

## Limits

Checks were run by the contributor, not by an organizer-designated verifier.
The independent implementation refers to NaNoda, not to an independent human
review. Dependency caches and network access were used; a full offline rebuild
of every foundational dependency is not claimed. The local environment used a
Lean frontend through Lake because it could not launch the ordinary lean
executable; the public run supplies the standard build and replay evidence.

Permanent independently administered archival, organizer review, mathematical
scope/priority adjudication and recipient confirmation remain pending. No
catalog eligibility, award allocation or payment entitlement is asserted.
