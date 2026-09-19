# Actual verification evidence

## Fixed source and successful run

- Proof repository: [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean).
- Exact proof commit: `d606af2009f85d5060008a1df249045c18ac34f3`.
- Project: `projects/jsp-000843`.
- [Successful proof workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169084966), job `105036620260`.
- Lean: 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`; all transitive revisions are locked in lake-manifest.json and compared to actual checkouts.
- Source Lean SHA-256: `63beb7e287084ee045d61d051665651762ffece0c9ee402064e4cbf747b03806`.

## Results

The workflow built the project with `lake build --wfail`, replayed the JSP000843
module using the bundled `leanchecker`, ran eight named declaration axiom audits,
verified all actual dependency revisions, and rejected the deliberately false
arithmetic statement `(1 : Nat) = 0`.

The eight target audits permitted only `propext`, `Classical.choice`, and
`Quot.sound`. No proof-hole or compiler-trust axiom was allowed.

The independently implemented NaNoda checker then checked **6,766 declarations
with no errors**. The exported dependency closures include both main quantified
existence statements and the key construction, coloring, cardinality and
definition-equivalence lemmas. The exporter and checker commits are pinned in
scripts/verify_nanoda.sh; the strict allowlist has unpermitted-axiom hard errors.

The [workflow job log](evidence/workflow-job.log) is the actual decoded API log,
preserved without removing timestamps or terminal control sequences.
The [artifact metadata](evidence/artifact-metadata.json) records GitHub's
archive digest and retention. The digest is GitHub's reported digest; no
independent local archive-download hash check is claimed.

## Retention and reproducibility

Full exported proof and reports: artifact `10475906905`, 4,136,526 bytes,
[artifact link](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169084966/artifacts/10475906905).
Reported SHA-256:
`b4c29318d947b6f74ece2c2d4126014b9f493d5e37573478c7955fad7fb9ec9b`.
Expires: 2026-12-16T01:04:05Z. The export can be reproduced with the pinned source
and scripts. No permanent independent archive or offline full-Mathlib rebuild is claimed.

These are contributor-run checks on a hosted runner, not independent human review
or organizer approval. The successful formal check establishes the stated known
component; the original problem's precise asymptotic questions remain open.
No award or payment is certified by these checks.

## Review requested

Please review fidelity to the scoped mathematical theorem, attribution, duplicate
or overlapping formalizations, public intake placement and eligibility.
Recipient placeholder: `RECIPIENT-JSP-000843-KZ-A`; written confirmation pending.
