# Verification receipt — 2026-09-17

## Tested source

- Proof repository: `ketianzhang1-lang/jsp-000301-lean`.
- Commit: `61368d8d5c75eb4854ba9c057933c20446f5d4cc`.
- Path: `projects/jsp-000636/JSP000636.lean`.
- Source bytes: 9,467.
- Source SHA-256: `ea51a6baca6bed306a1b71c4fc2023429c6fdf47f00284cc727638afa5284640`.
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- The copied proof, audit, licenses, dependency pins and reproduction scripts
  are unchanged from the tested source package.

## Actual results

[Run 35172497300](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172497300),
job `105046956109`, completed successfully at the tested commit.

| Check | Result |
| --- | --- |
| `lake build --wfail` | Passed; 3,093 jobs |
| `lake env leanchecker JSP000636` | Passed |
| Axiom audit of all 14 project theorems | Only `propext`, `Classical.choice`, `Quot.sound` |
| Actual dependency commits compared with manifest | Passed |
| False-arithmetic control | Rejected as required |
| NaNoda | 5,565 declarations checked; no errors |

NaNoda used exporter commit `6cea97789dc088ea47fcea15692db85685aedac5`
and checker commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
The configuration permits only the three axioms above and enables hard
failure for unpermitted axioms. Exported target closures were
`size_count_le`, `exact_multiplicity_card_le`, `sharp_at_four`,
`three_is_exception`, and `one_is_exception`, all in namespace JSP000636.
The exact configuration and commands are in `scripts/verify_nanoda.sh`.

Before publication, local Lean compilation with warnings as errors,
bundled kernel replay and all 14 axiom audits also succeeded. The CI results
above provide the independently reproducible clean-run evidence.

## Evidence archive

- [Artifact 10477053133](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172497300/artifacts/10477053133).
- Name: `jsp-000636-evidence`.
- ZIP size reported by GitHub: 3,716,420 bytes.
- ZIP SHA-256 reported by GitHub:
  `173de04ae43ba3df2d64b5757aa61c76b4a44eb69f42d7dab4cdce0bda209ad7`.
- API expiry: `2026-12-16T01:56:50Z`.

This artifact contains the build and axiom logs, negative control output,
NaNoda configuration and compressed export, dependency manifest and a source
archive. The digest and size above are GitHub metadata; the ZIP was not
downloaded and independently rehashed in this session.

A [selected CI log excerpt](ci-verification-excerpt.log) is preserved in this
Git commit so key results remain available after Actions retention expires.
It is not a permanent copy of the complete artifact or checker export.
`SHA256SUMS` records all packet files other than itself.

## Limits

Official repository preflight at base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae` passed locally:
`validate`, `links`, `build`, `check`, `history`, and all 22 existing validator
tests. All source copies and packet hashes matched, and generated indexes
were unchanged. These are repository-integrity checks, not mathematical
or award decisions.

Lean's bundled checker uses the Lean kernel. NaNoda is a separate checker
implementation; neither check is an independent human review or an
organizer decision. Checking a formal proposition does not by itself
establish its mathematical originality, fidelity to every part of the
original question, priority, or prize eligibility. The scope limitation in
README and REVIEW_REQUEST is essential: this proves the universal upper
bound, not the threshold n₀(r).
