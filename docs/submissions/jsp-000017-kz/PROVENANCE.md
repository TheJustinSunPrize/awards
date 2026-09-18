# Provenance

## Mathematical results

This submission concerns known special cases of JSP-000017. The elementary
three-runner case is classical. The consecutive doubling-speed condition is
credited to Javier Barajas and Oriol Serra by Theorem 18 of the survey by
Guillem Perarnau and Oriol Serra, *The Lonely Runner Conjecture turns 60*,
[arXiv:2409.20160v3](https://arxiv.org/abs/2409.20160v3), Sections 6.1 and 7.3.
The new code uses a direct real-interval proof, allowing signed real relative
velocities. This is not claimed as a newly discovered mathematical result or
as a stronger result than all existing literature.

## Formalization

Proof repository: `ketianzhang1-lang/jsp-000301-lean`.

Immutable proof commit: `ba03ade383e1c8dc00008a6200c15232dad43cf9`.

Path: `projects/jsp-000017/`.

The Lean proof and interval lemmas were written with OpenAI ChatGPT/Codex
assistance for this package. The primary dependency is Mathlib; no external
lonely-runner proof package is imported. The final three-runner predicate
adapter follows the existing Formal Conjectures mathematical statement and
does not claim its authorship. Repository verification scripts adapt the
submitting account's prior proof-verification workflow.

The eight proof-project files in this submission are byte-for-byte copies of
that immutable proof commit. Additional submission-specific files record
scope, provenance and verification receipts. `PROOF_SHA256SUMS` identifies the
eight original files.

## Prior-work search and limits

A search of the official repository's issues and pull requests for
`JSP-000017` on 2026-09-17 returned no matching entries at preparation time.
Global GitHub searches returned existing lonely-runner certificate projects;
the search is not exhaustive and is not a priority certificate. Those projects
are not copied or represented as this contributor's work. Formal Conjectures
already contains the general statement and a separate Tao-bound statement.
This package proves neither the unrestricted general conjecture nor Tao's
asymptotic bound.

## Proposed contribution

Please assess the independently written formalization, statement fidelity,
reproduction, overlap, attribution and eligibility as a scoped contribution.
The official whole-problem eligibility flag is still No. The package does not
create an award, record a confirmed recipient, or authorize payment.

Proposed recipient: `RECIPIENT-JSP-000017-KZ-A`, confirmation pending.
This is a self-submission and its checks are contributor-run.
