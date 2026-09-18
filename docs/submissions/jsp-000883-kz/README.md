# JSP-000883: Monier bound and an infinite family of starting points

Please review this self-submitted Lean formalization of a **known component**
of [JSP-000883 / Erdos 1063](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000883).

For every `k >= 3`, and every positive integer `a`, the starting point
`N = a*k!` satisfies `N >= 2*k`, and exactly one of
`N, N-1, ..., N-k+1` fails to divide `choose(N,k)`: that exception is `N`.
Consequently the original least-starting-point function satisfies
`2*k <= n(k) <= k!`, and the set of admissible starting points is infinite.
The least-element definition is proved to attain an admissible value.

## Exact scope and attribution

The known factorial upper bound is credited to **Jean-Marie Monier (1985)**.
The definition and compatibility theorem type are adapted from **The Formal
Conjectures Authors (2026)**, Apache 2.0. The implementation was independently
written with **OpenAI ChatGPT assistance** under the submitting account's
direction. Mathlib infrastructure is acknowledged.

This does not prove Cambie's stronger least-common-multiple bound, improve it,
classify all starting points, or solve the full original problem. No change
to the catalog's Progress or eligibility fields is requested. No new
mathematics, worldwide first-formalization priority, independent reviewer
role, award allocation or payment entitlement is asserted.

## Public evidence

- [Pinned proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d951a581d98d209c168ec4066af97df52a7a9498/projects/jsp-000883).
- [Proof verification workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35174825512).
- [Pinned original statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean).
- `PROOF.md`: elementary argument, mathematical scope, sources and reproduction.
- `VERIFICATION.md`: completed checks and their limitations.
- `SOURCE_SHA256SUMS`: byte-for-byte source checksums. `PROOF.md` is the
  original proof-project `README.md` under a different filename.

## Review request

Proposed recipient placeholder: `RECIPIENT-JSP-000883-KZ-A`.
Confirmation status: **pending**; no authorized public attestation of written
recipient confirmation is supplied. This is not a confirmed public profile.

Please assess statement fidelity, contribution scope, attribution, overlap,
eligibility and the appropriate intake route. Contributor-run automated
checks do not establish organizer acceptance or a prize award.
