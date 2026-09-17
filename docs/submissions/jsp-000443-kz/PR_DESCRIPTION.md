## Change

Please assess a **partial formalization contribution** for JSP-000443 / Erdős 552. This does not solve the original all-parameter question or its unbounded-deficit variant. The mathematical bounds and finite construction are known; mathematical novelty and first-formalization priority are not claimed.

The Lean package proves, with K1,n denoting a star with n leaves:

- For every natural n, R(C4,K1,n) <= n + floor(sqrt(n)) + 2.
- For positive even k, R(C4,K1,k^2) <= k^2 + k + 1.
- R(C4,K1,16) = 21, using a kernel-checked 20-vertex graph obtained from a GF(4) polarity construction.

It also proves equivalence of its containment predicates with Mathlib graph copies of cycleGraph 4 and completeBipartiteGraph (Fin 1) (Fin n). The finite graph generator is reproduction support, not a trusted proof oracle.

- [Review request and source package](https://github.com/ketianzhang1-lang/awards/tree/96b0c41d652a129ed582041e9da3b70574911974/docs/submissions/jsp-000443-kz)
- [Pinned, tested proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/0a78950267f4b292414624f8cd8e15c074c14850/projects/jsp-000443)
- [Successful public verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172429626)

## Verification evidence

The fixed proof commit passed Lean 4.34.0 compilation with warnings as errors, bundled leanchecker replay, nine target axiom audits, all nine dependency revision checks, a false-arithmetic negative control, and exact graph-row reproduction. Mathlib is pinned to 5ed2965256430c3649e86755f9576b54eca72435.

Pinned lean4export and NaNoda independently checked the five endpoint dependency closures: **8,737 declarations, no errors**, allowing only propext, Classical.choice and Quot.sound. The audit rejects sorryAx and compiler-trust axioms. These are contributor-run checks with an independently implemented checker, not an independent human review or organizer certification.

The external Actions artifact has ID 10476958624, 5,513,816 bytes, and GitHub-reported ZIP SHA-256 cbc6e6eaf516b653264a3b0ec044a1a8c9f88311398f8babeaff463900803f1c. Its advertised expiry is 2026-12-16; **permanent independent archival remains pending**. The ZIP could not be materialized locally through the connector, so a separately recalculated local ZIP digest is not claimed. Fixed repository commits preserve source, historical local receipts, and a clearly labeled cloud-log excerpt. See VERIFICATION.md for all limits and checker pins.

## Record or policy impact

This PR only adds docs/submissions/jsp-000443-kz/. It changes no catalog eligibility, candidate, award, recipient confirmation, payout, or published decision. The whole-problem catalog remains Progress / Lean No / Eligible No / Unavailable.

This is a self-submission, prepared with OpenAI ChatGPT assistance. The proposed contributor is the unconfirmed placeholder RECIPIENT-JSP-000443-KZ-A. Classical background and original problem references are attributed in README.md and PROVENANCE.md. No curator or designated verifier role is claimed.

Please review statement fidelity, attribution, overlap, scope and whether any formalization-contribution pathway applies. No award allocation or payment entitlement is asserted.

## Checks

- [x] All submission text is in English; it does not announce an award.
- [x] The proposed recipient uses an unconfirmed placeholder; no private contact/payment details or committee deliberations are included.
- [ ] Permanent independent verification archive completed. A finite-retention external artifact and its reported ID/digest/size are documented above.
- [x] Published statements and decisions are preserved.
- [x] python scripts/manage.py validate and links pass.
- [x] build has run and check passes; generated indexes are unchanged.
- [x] history passes against f4e7173d89dfe91022a185427d63452c8ffbf6ae.
- [x] All 22 organizer validator tests pass; no validator code was changed.
- [x] Nine proof/reproduction files match the pinned tested proof tree byte-for-byte.

## Requested reviewer decision

Please assess this scoped contribution and advise whether it can enter any applicable review/eligibility process, with the pending archive and human-review gates explicitly retained. A green repository check is not mathematical approval or permission to pay.
