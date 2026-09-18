## Infinite-family supplement — 2026-09-17

This updates existing PR #379 with a uniform finite-field proof. For every
positive natural r, with q = 2^r, Lean proves

**R(C4,K1,q^2) = q^2 + q + 1.**

K1,n denotes the star with n leaves; copies are ordinary, not induced.
The construction works over arbitrary finite fields for the lower bound;
even field order gives equality. This covers all positive exponents and
includes R(C4,K1,64)=73 and R(C4,K1,256)=273. It retains the original
universal square-root upper bound, even-square upper bound, exact n=16
certificate, and Mathlib graph-copy equivalences.

**Partial scope:** this does not determine all star Ramsey numbers or settle
the original unbounded-deficit question. The polarity construction and its
Ramsey consequence are known mathematics. Parsons and the other original
sources retain credit. No mathematical novelty or global first-formalization
priority is claimed. OpenAI ChatGPT assistance is disclosed.

## Fixed source and verification

- [Tested source a6b9188](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/a6b9188dea3d13d3c6c67ea1da6a5fd87045ec7f/projects/jsp-000443).
- [Successful cloud run 35176333614](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176333614).
- [Mathematical construction](FAMILY_PROOF.md), [complete receipt](FAMILY_VERIFICATION.md), [source hashes](FAMILY_SOURCE_SHA256SUMS), and [attribution and overlap](PROVENANCE.md).

Lean 4.34.0 with pinned Mathlib and all transitive dependencies. The build
with warnings as errors, both kernel replays, all sixteen axiom audits,
dependency checks, false-arithmetic negative control, and finite-witness
reconstruction passed. Pinned NaNoda checked **21,448 declarations without
errors**, allowing only propext, Classical.choice and Quot.sound.

The external artifact is 10479055490, 17,716,297 bytes, with service-reported
ZIP SHA-256 56cb74e591bd0efe9d4f4340a6d511fa1ba38f60996cbe36267e7d05591b7fcd.
Advertised expiry: 2026-12-16. The receipt distinguishes service-reported
metadata from local hash recomputation and records finite-retention and
cached-library limits. These are contributor-run checks, including a second
checker implementation; independent human or organizer review is not claimed.

All 22 repository tests and validate/links/build/check/history passed.
The original proof module is unchanged; initial verification receipts and
the initial PR description are preserved with clearly identified scope.

## Prior work and review request

Earlier [PR #134](https://github.com/TheJustinSunPrize/awards/pull/134)
formalizes Boza's Theorem 6 and Corollary 8 for the same problem. Its stated
targets are different inequalities; this comparison and its limits are
recorded in PROVENANCE.md. Please assess overlap and the incremental value
of this independently written finite-field implementation.

Proposed recipient: RECIPIENT-JSP-000443-KZ-A, confirmation pending.
This is a self-submission for formalization-contribution review. Only the
existing submission directory is changed; no catalog eligibility, candidate,
award, recipient confirmation or payment record is changed. No separate
reward request is made for individual parameters. Please assess statement
fidelity, attribution, scope, significance and any applicable eligibility.
