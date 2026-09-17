# Verification receipt

## Exact proof source

- Commit: `59c5b5540c469b13e7b4848c7c3fbd17e688f519`.
- [Proof directory](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/59c5b5540c469b13e7b4848c7c3fbd17e688f519/projects/jsp-000295).
- [Proof CI run 35171855423](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423), job `105045009825`.
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The proof source was fetched again from GitHub at the pinned commit and compared
byte for byte to all ten project files copied here. The proof README is retained
as PROOF.md; its bytes are unchanged. SOURCE_SHA256SUMS records these files.

## Actual completed checks, September 17, 2026 UTC

- `lake build --wfail` passed: 3,095 jobs.
- Bundled kernel replay passed separately for JSP000295, Compatibility and Audit.
- Nine named target axiom audits passed. Only `propext`, `Classical.choice` and
  `Quot.sound` are allowed; no admitted proof or native-evaluation axiom is used.
- All transitive dependency revisions matched the lockfile.
- The false-arithmetic negative control was rejected.
- Pinned NaNoda, with a hard-error allowlist for the same three axioms, checked
  the exported dependency closures and reported **13,975 declarations, no errors**.
- The manifest remained unchanged during the workflow.

The exported targets include the original-shape compatibility theorem and the
explicit all-n bound. `evidence/ci-excerpt.log` is a selected timestamped excerpt
from the actual job log, not the complete log. Compact complete logs from the
artifact are retained alongside it where available.

## Full workflow artifact

- [Artifact 10476748299](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171855423/artifacts/10476748299).
- ZIP size: **9,228,096 bytes**.
- ZIP SHA-256: `90a76dc095ab57ff3c46dff0573af4a6e7a65873172e3858113a9cf6a034b99b`.
- Scheduled expiration: **2026-12-16 01:46:35 UTC**.

This ZIP contains tested source, build and kernel logs, axiom output, the negative
control log, the exported proof closure, NaNoda configuration and checker output.
The artifact's finite retention is disclosed; no permanent external archive is
claimed. Compact source and receipts are also retained in this submission's Git
history. These hashes identify evidence; they do not certify mathematical scope.

The ZIP was downloaded and its actual byte count and SHA-256 verified locally.
Every project file in the tested source archive was also compared byte for byte
against the project fetched at the pinned commit. The compact original build,
kernel, axiom, negative-control and NaNoda logs are retained in `evidence/`.

## Repository checks

All 22 official repository tests passed. The official validate, links, build,
check and history commands passed against base commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. The command receipts and original test
output are included in `evidence/`. Only the new submission directory is added.

`git diff --check` reports one extra final blank line in the unchanged pinned
NaNoda script and one in NaNoda's original pretty-printer transcript. Both are
retained byte for byte; these are formatting notices, not proof or validator
failures. No whitespace-clean claim is made for those two evidence/source files.

## Reproduction and limits

Run the commands in PROOF.md in the locked project. The two verification scripts
and pinned checker commits are included. GitHub Actions uses cached Mathlib;
there was no from-source rebuild of the complete imported library and compiler.
Bundled leanchecker reuses Lean's kernel; NaNoda is a separate implementation.
All checks were contributor-run. Independent human review and organizer decisions
on attribution, overlap and eligibility remain pending.

The theorem is a complete proof of the known lower-bound component. It leaves
the original f(n)=o(n) question and exact growth rate open. Neither successful
proof checking nor repository validation authorizes an award or payment.
