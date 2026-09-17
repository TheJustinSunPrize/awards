# Verification receipt — 17 September 2026

## Exact proof source and scope

Proof repository: `ketianzhang1-lang/jsp-000301-lean`.
Verified commit: `2a6c737b5fb409a5600918cc5a2bab0a8dd174bb`.
Directory: `projects/jsp-000554`.
[Pinned source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/2a6c737b5fb409a5600918cc5a2bab0a8dd174bb/projects/jsp-000554).

The exact statements, definitions, mathematical sources and limits are in
[README.md](README.md). This is partial formalization of an unconditional
reduction in Gafni–Tao, with small-gap corollaries. The original asymptotic
prime-gap question is not claimed solved by this package.

## Actual clean-run results

[GitHub Actions run 35169457743](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169457743)
completed successfully on Ubuntu 24.04 at the pinned commit.

| Check | Result |
| --- | --- |
| `lake build --wfail` | Passed, 2,278 jobs |
| Bundled `leanchecker JSP000554` | Passed, exit 0 |
| Twelve declared target axiom audits | Only `propext`, `Classical.choice`, `Quot.sound` |
| All locked dependency revisions | Matched |
| False-arithmetic control `1 = 0` | Rejected as required |
| Python residue-table diagnostic | Six tables matched |
| Independent NaNoda replay | 31,572 declarations, no errors |
| Source archive comparison | Every archived source file byte-identical to this package |

The empty [kernel.log](evidence/kernel.log) is the checker's actual successful
output; its exit status is enforced by `set -euo pipefail` in the successful
workflow. See the compact [build](evidence/build.log),
[axiom](evidence/axioms.log), [NaNoda](evidence/nanoda.log),
[pretty-printed statements](evidence/nanoda-statements.txt), and
[negative-control](evidence/negative-control.log) reports.

NaNoda was pinned to `4c544ed4099c8227f07d5de77ad1e69fb0740a27`;
lean4export to `6cea97789dc088ea47fcea15692db85685aedac5`.
The [configuration](evidence/nanoda-config.json) has a strict three-axiom
allowlist and rejects unpermitted axioms. Nat and string extensions are enabled.
The exporter checked the dependency closures of the general reduction, exact
counting identity, and all six small-gap classification targets.

## Artifact and retention

Full artifact: `10476087314`, `jsp-000554-evidence`, 30,053,577 bytes.
[Artifact link](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169457743/artifacts/10476087314).

ZIP SHA-256:
`e4e8650fd4694d6fb251926d2dd80712a786c22a36a3a1e2858f2c97f4e77cab`.
The downloaded ZIP was checked against this hash. The compressed proof export
is 30,079,545 bytes before ZIP wrapping; its own checksum is in
[CHECKER_SHA256SUMS](evidence/CHECKER_SHA256SUMS).
The full archive has finite retention through 16 December 2026. The source,
reproduction scripts, manifest and compact reports are included here; no
independent permanent archival of the large export is claimed.

## Repository checks and limits

All 22 official repository tests and `validate`, `links`, `build`, `check`,
and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae` passed locally.
The [preflight log](evidence/repository-preflight.log) records the initial package
check; the final package was rechecked after adding this receipt and reports.
Existing catalog, candidate, award and recipient records are unchanged.

These are contributor-run verification records, not organizer acceptance or
independent human review. CI used network access and cached Mathlib artifacts;
an offline full-Mathlib rebuild is not claimed. The initial CI attempt failed
because a finite-product coprimality import was missing; the successful commit
explicitly imports it. No linter, proof statement, or verifier was weakened.

Review of statement fidelity, attribution, overlap, priority, intake placement,
and partial-contribution eligibility remains with the organizers. No award,
allocation, or payment entitlement is asserted.
