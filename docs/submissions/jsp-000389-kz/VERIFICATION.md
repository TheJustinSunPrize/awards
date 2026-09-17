# Verification receipt: 17 September 2026

## Exact source and scope

Proof repository: `ketianzhang1-lang/jsp-000301-lean`.
Commit: `3ab06d1f57b76a0573da1003b126f1df4a96abda`.
Directory: `projects/jsp-000389`.
[Pinned source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/3ab06d1f57b76a0573da1003b126f1df4a96abda/projects/jsp-000389).

The four components and their original sources are specified in [README.md](README.md).
The implementation is a partial formalization contribution relative to the
original open problem, not a solution of the asymptotic conjecture.

## Actual automated results

[Proof CI run 35171609997](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171609997)
completed successfully at the pinned commit on Ubuntu 24.04.

| Check | Observed result |
| --- | --- |
| Lean `lake build --wfail` | Passed, 3,096 jobs |
| Bundled `leanchecker JSP000389` | Passed, exit 0 |
| Eight target axiom closures | Only `propext`, `Classical.choice`, `Quot.sound` |
| Locked dependency revisions | All matched |
| False arithmetic `1 = 0` | Rejected as required |
| Independent NaNoda replay | 14,542 declarations checked, no errors |
| Published source readback | Main Lean source matched byte for byte |
| CI source archive | All eight source/reproduction files matched the submitted package |

See the actual [build](evidence/build.log), [axiom](evidence/axioms.log),
[kernel](evidence/kernel.log), [NaNoda](evidence/nanoda.log),
[exported statements](evidence/nanoda-statements.txt), and
[negative control](evidence/negative-control.log) reports.
The kernel log is empty because successful execution emitted no output;
its exit status was enforced by the successful workflow script.

NaNoda revision: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
lean4export revision: `6cea97789dc088ea47fcea15692db85685aedac5`.
The [configuration](evidence/nanoda-config.json) uses a strict three-axiom
allowlist with hard errors for unpermitted axioms. Nat and string extensions
are enabled. The exported closures include both main bounds, the combined
necessary-conditions theorem and the missing-residue theorem.
The submitted proof contains no proof holes, custom axioms or native-evaluation
proof shortcuts.

## Archived artifact

[Artifact 10476144763](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171609997/artifacts/10476144763):
`jsp-000389-evidence`, 10,368,924 bytes.

ZIP SHA-256:
`aaad20a4046b506184a0d8f885f679cacad167a8e200576c973814566354556d`.

The ZIP was downloaded and its exact byte count and digest verified. Its
`SOURCE_COMMIT` matches the pinned source. The tested source archive was
compared against the eight corresponding files in this package. Export and
source-archive checksums are preserved in the evidence directory.
GitHub currently advertises expiry on 16 December 2026. Source, reproduction
scripts and compact reports are preserved in this submission; independent
permanent archival of the full export is not claimed.

## Repository checks and limitations

All 22 official repository tests passed. The official `validate`, `links`,
`build`, and `check` commands passed. The finalized package is checked again
with the history-preservation gate in the accompanying
[preflight record](evidence/repository-preflight.log).
No existing catalog, candidate, award, recipient, schema or validator file is changed.

These are contributor-run checks, not organizer acceptance or independent
human certification. Network access and cached Mathlib artifacts were used;
an offline full-library rebuild and organizer minimum-safe-version approval
are not claimed. The independently implemented checker adds evidence but does
not establish eligibility. Scope, fidelity, attribution, overlap, priority,
recipient confirmation and award decisions remain for organizer review.
