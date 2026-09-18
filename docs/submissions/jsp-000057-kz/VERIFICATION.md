# Verification evidence for JSP-000057 (scoped case)

This is contributor-generated verification evidence, not an organizer decision
or an independent human review. "Independent checker" below refers to a
separate checker implementation run by the contributor.

## Checked source and environment

| Item | Value |
| --- | --- |
| Proof repository | `ketianzhang1-lang/jsp-000301-lean` |
| Proof commit | `b45035ab53aece620f2029e0e73c7e8146718cd1` |
| Project | `projects/jsp-000057` |
| Lean | `leanprover/lean4:v4.34.0` |
| Mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Dependency lock | [lake-manifest.json](source/lake-manifest.json) |
| Runner | GitHub-hosted `ubuntu-24.04` |
| Workflow run | [35177146542](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177146542) |
| Verification job | `105061240959` |
| Result | Completed successfully on September 17, 2026 |

The workflow pins checkout/artifact actions, uses read-only repository
permissions, and checks actual dependency Git revisions against the lockfile.
This is reproducible contributor CI with network access, not the organizer's
isolated offline verification.

## Observed checks

| Check | Result |
| --- | --- |
| `lake build --wfail` | Success, 3,093 build jobs |
| Bundled `leanchecker JSP000057` | Exit success |
| Eight theorem axiom closures | Only `propext`, `Classical.choice`, `Quot.sound` |
| Explicit target types | Numerical equation and original predicate checked in `Audit.lean` |
| False arithmetic negative control | `1 = 0` rejected by Lean |
| Strict-allowlist NaNoda | 7,399 declarations checked without errors |
| Downloaded artifact ZIP | Byte count and SHA-256 matched GitHub's artifact metadata |
| Archived source | All 12 project files matched the submitted source byte-for-byte |

The audited declarations are `matching_of_card`, `seven_forces_three`,
`twoTriangles_no_three`, `threshold_iff`, `seven_forces_three_sets`,
`twoTriangles_sets_no_three`, `original_threshold_iff`, and `f_two_three`,
all in namespace `JSP000057`. Their checked types and standard axioms appear
in [nanoda-statements.txt](evidence/nanoda-statements.txt).

- lean4export pin: `6cea97789dc088ea47fcea15692db85685aedac5`.
- NaNoda pin: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
- [Checker configuration](evidence/nanoda-config.json) hard-fails on axioms
  outside the three-axiom allowlist and checks the exported theorem closures.
- [Build log](evidence/build.log), [axiom log](evidence/axioms.log),
  [checker log](evidence/nanoda.log), and [negative control](evidence/negative-control.log).

## Artifact identity and retention

The full machine artifact is
[jsp-000057-evidence](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177146542/artifacts/10479296952),
artifact ID `10479296952`, **4,551,344 bytes**.

- ZIP SHA-256: `e7bd2f81fe64d71fac3b6cc4c1fffdde5aab20dc8264528376a84e16ff68a741`.
- Source archive SHA-256: `c69071262713c76e151e8b8c5c9b9758709322b7469f62facd63a8441d7f37c7`.
- Compressed export SHA-256: `988b927be0b047a616c0371898ed30dd41f8d1da809cb6d46032c4c6b9d0a483`.
- Main Lean module SHA-256: `b403a1246faf129abccfecf92facc6b50599975537c76102c1975d41179c8803`.

The Actions artifact expires on **December 16, 2026**; it is not a permanent
archive. The source, scripts, lockfile, small logs, checked statements, and
hashes are included in this Git submission so verification can be reproduced
after expiry. The large export and source tarball remain in the referenced
artifact. A permanent archive can be added by a designated verifier if needed
for formal intake.

## Statement fidelity and limits

The exact result is the classical special case `f(2,3) = 7`, with the
same threshold and sunflower definitions as the pinned Formal Conjectures
source. Both lower and upper bounds are established.
`original_threshold_iff` identifies the entire set defining the infimum as
`{m | 7 <= m}`; no empty-infimum convention is used to obtain the result.
Finite-family conversion preserves cardinality, membership, and the
sunflower predicate. See [STATEMENT.md](source/STATEMENT.md).

The main sunflower conjecture remains open in this submission. This work
makes no new-mathematics, improved-known-bound, or first-formalization claim.
Organizer verification, contribution eligibility, overlap/attribution review,
recipient confirmation, and award adjudication remain pending.
