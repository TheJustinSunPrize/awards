# Verification receipt — JSP-000636 expanded threshold supplement

## Pinned source and actual CI result

- Proof commit: `d5fc3ee7fc5a452e8104b5099c854a5a15a668bf`.
- [Source package](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d5fc3ee7fc5a452e8104b5099c854a5a15a668bf/projects/jsp-000636).
- [CI run 35177799617](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177799617): completed successfully, 2026-09-17 UTC.
- Verification job: `105063250601`, all steps successful.
- [Evidence artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177799617/artifacts/10478897431): `10478897431`, 5,276,359 bytes.
- Artifact SHA-256: `45af682158a67d2d65d7d5eb0713417e7779be6c1cd407b46eb4a52d12e6b897`.

The six mathematical modules, Audit, compiler/dependency pins, lakefile,
and verification scripts in this packet match that pinned proof commit.
This receipt and review documents report later evidence and are not part
of the mathematical dependency closure. The proof commit extends
`3e3bb53650eda1f183b5af89ea3f6747349c06a4`; the inherited core and lower-bound
modules are unchanged.

## Checks actually completed

A fresh Ubuntu CI runner installed Lean 4.34.0 and the pinned Mathlib
cache. All of the following completed successfully:

1. `lake build --wfail`: all six modules compiled with warnings as errors.
2. Lean's bundled `leanchecker`: replay of all six modules.
3. All **61** theorem axiom audits, allowing only `propext`,
   `Classical.choice`, and `Quot.sound`.
4. All dependency Git revisions checked against `lake-manifest.json`.
5. False arithmetic `1 = 0` rejected as a negative control.
6. Separate NaNoda checker: **7,375 declarations checked, no errors**.
7. Source, manifest, logs, export and checksums archived as CI evidence.

The independent exporter is pinned to
`leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5`;
the checker is pinned to
`ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
NaNoda used `unpermitted_axiom_hard_error=true` and the same strict
three-axiom allowlist. Exported targets include the main universal and
critical bounds, attaining-family existence, eventual equality,
threshold existence, least-threshold specification/minimality/bounds,
levelwise thinning, and exact attaining families, together with their
complete dependency closures.

The observed log reports:

```text
All 61 theorem axiom audits and dependency pins passed.
False arithmetic rejected as required.
Checked 7375 declarations with no errors
```

Selected actual log lines are retained in
[ci-verification-excerpt.log](ci-verification-excerpt.log).
Lean's bundled kernel replay is not an independent implementation;
NaNoda is the separate implementation used here.

Local checks also passed before publication. Local dependency Git HEADs
were incomplete in the reused cache, so revision verification is claimed
on the basis of the successful fresh CI check above.

## Awards repository preflight

All 22 repository unit tests passed. `validate`, `build`, `check`,
`links`, and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae`
passed in the isolated review checkout. Generated JSON stayed unchanged.
The submitted changes are confined to this documentation/proof packet.

## Limits

The successful checks validate the stated partial formalization. They do
not establish the paper's logarithmic threshold bound, exact small-r
thresholds, full resolution of JSP-000636, global first priority,
independent human review, organizer acceptance, eligibility or payment.
No catalog eligibility flag, candidate record or award record is changed.
