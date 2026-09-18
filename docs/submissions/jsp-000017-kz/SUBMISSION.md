# Prepared pull request description

## Requested review

Please review this scoped Lean formalization contribution for JSP-000017 (Lonely Runner Conjecture), including statement fidelity, overlap, attribution, and whether it is eligible for contribution recognition under the prize's rules.

This is a formalization of **known special cases**, not a solution of the unrestricted conjecture and not a claim of new mathematics or first formalization priority. The catalog's whole-problem flags remain Open / Lean proof No / Eligible to claim No.

## What is proved

- **Complete three-runner case:** arbitrary distinct signed real speeds; every chosen runner has a strictly positive time at circular distance at least `1/3` from each other runner.
- **Doubling relative-speed family for arbitrary finite runner counts:** for a chosen reference runner, if the absolute relative speeds of all other runners can be ordered with consecutive ratios at least two, a common strictly positive time achieves distance at least the reciprocal of the total runner count. Coverage of all competitors and the additional doubling hypothesis are explicit.
- Statements use Mathlib's actual `UnitAddCircle` metric. An adapter matches the existing Formal Conjectures loneliness-predicate interface for three runners.

The three-runner result is classical. The doubling family is credited to Javier Barajas and Oriol Serra in Theorem 18 of Perarnau and Serra's [survey](https://arxiv.org/abs/2409.20160v3). The package documents these credits and prior-search limits. The independently written Lean code was produced with OpenAI ChatGPT/Codex assistance.

## Evidence

- [Immutable proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/ba03ade383e1c8dc00008a6200c15232dad43cf9/projects/jsp-000017)
- [Successful verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171971482) at that exact commit
- Lean 4.34.0, fully locked package revisions, warnings-as-errors build, Lean checker replay, eight axiom audits, and a rejected false-arithmetic negative control
- Pinned NaNoda checked **13,647 declarations with no errors**, allowing only `propext`, `Classical.choice`, and `Quot.sound`
- [Artifact 10476873166](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171971482/artifacts/10476873166): 8,775,996 bytes; reported ZIP SHA-256 `8172795267b73a1adc7e6e12093de4708e8ad17526d1fc9c0264d36e20bcbe71`; reported expiry 2026-12-16
- The evidence directory contains byte-identical proof-project copies, source hashes, statement comparison, provenance, compact public run receipts and reproduction instructions.

These are contributor-run checks, including an independent checker implementation, not independent human certification or organizer approval. Dependency caches were used. Artifact size/hash are the mutually consistent upload-log/API values; a separate local ZIP digest was not recomputed because the temporary download returned HTTP 403. Finite artifact retention and that transfer limitation are disclosed in the receipt.

## Repository scope and preflight

Only `docs/submissions/jsp-000017-kz/` is added. No catalog, candidate, recipient, award or payment status is changed.

Repository validation, links, data generation, generated-data consistency and history checks pass; all 22 repository unit tests passed. The source tree uploaded to the fork matches the locally checked tree exactly. These structural checks do not decide mathematical validity or awards.

Proposed recipient: `RECIPIENT-JSP-000017-KZ-A`, confirmation pending. This is a self-submission with a direct interest in the review outcome. No private identity or payment information is included.

Please advise the appropriate intake placement if a different evidence format is preferred.
