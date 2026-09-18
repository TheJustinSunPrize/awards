# Verification and archive record — 2026-09-17

## Fixed source and actual cloud result

- Proof repository: `ketianzhang1-lang/jsp-000301-lean`.
- Commit: `0a78950267f4b292414624f8cd8e15c074c14850`.
- Directory: `projects/jsp-000443`.
- [Successful proof workflow, run 35172429626](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172429626).
- Job: `105046747876`, `verify`, completed successfully.
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

The cloud run completed `lake build --wfail` (3,131 jobs), an explicit
`leanchecker JSP000443` replay, nine named axiom audits, all nine dependency
revision checks, rejection of a false arithmetic control, and independent
Python reproduction of the graph rows. No proof source was changed for the
cloud run. The published proof tree was fetched back and matched the
locally checked tree byte-for-byte.

All nine audited targets use only a subset of `propext`, `Classical.choice`
and `Quot.sound`. The exact n=16 theorem and both standard graph-copy
equivalences are among those targets. No `sorryAx`, compiler-trust axiom or
custom axiom is allowed by the audit. Literal graph checks use `decide +kernel`.

## Independently implemented checker

The successful run used lean4export commit
`6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27` (version 0.4.17).
NaNoda reported **8,737 declarations checked with no errors**.

The exported closures include the universal upper bound, even-square
upper bound, exact n=16 theorem, and both graph-copy equivalences.
The checker configuration sets `unpermitted_axiom_hard_error` to true and
permits only the three foundational axioms listed above. The exact source
script, pins and checker configuration construction are supplied in
`scripts/verify_nanoda.sh`.

The checker is an independent implementation; these checks were still
initiated by the contributor. They are not independent human review or
organizer certification.

## External artifact

| Field | Value |
| --- | --- |
| Artifact | `jsp-000443-evidence` |
| GitHub artifact ID | `10476958624` |
| Byte count reported by GitHub | `5513816` |
| ZIP SHA-256 reported by GitHub | `cbc6e6eaf516b653264a3b0ec044a1a8c9f88311398f8babeaff463900803f1c` |
| Advertised expiry | `2026-12-16T01:55:45Z` |

[Artifact download page](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172429626/artifacts/10476958624).

The artifact contains the source archive, build/replay/audit/control logs,
graph diagnostic, exported proof, NaNoda configuration, statement output
and checksums. Its ID, size and digest were cross-checked against the
GitHub metadata and successful upload log. Download through the connector
returned a file reference, but materializing its temporary URL in this
container returned HTTP 403. Thus no independent local recalculation of
the whole ZIP digest is claimed.

GitHub Actions retention is finite; this is not a permanent independent
archive. The immutable source and compact verification evidence are also
preserved in repository commits. Permanent external archival remains
pending and is not represented as a completed gate.

## Preserved evidence and remaining review

`verification/ci-excerpt.log` contains selected exact timestamped lines
from the decoded job log returned by the GitHub connector. It is an
excerpt, not the entire job log. Earlier local-only receipts are preserved
under `verification/`; `LOCAL_VERIFICATION.md` is the historical record.

The shared Mathlib cache and network access were used. This does not claim
an offline full-library rebuild, a complete replay of every library module,
official minimum-safe-version approval or designated verifier signatures.
Statement fidelity, attribution, overlap, priority and the eligibility of
this **partial** contribution remain for organizer assessment. No award or
payment entitlement is asserted.
