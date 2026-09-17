# Scope, attribution, and prior work

This project formalizes **Stijn Cambie's known least-common-multiple upper bound**: for every natural number `k ≥ 3`,

```lean
n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id
```

The definition of `n k` requires `n ≥ 2*k` and **exactly one** nondivisor among `n, …, n-k+1` of `Nat.choose n k`. The least common multiple is computed over the natural numbers.

The proof constructs `N = k*lcm(1,…,k-1)`, proves `N ≥ 2*k`, and identifies offset `0` as the unique exception. It supplies an actual member of the defining set and does not rely on the default infimum of an empty set. This is not a claim of new mathematics, a solution of the full growth-rate problem, or a formalization of an exponential asymptotic bound.

## Mathematical and formal sources

- [Erdős Problem 1063](https://www.erdosproblems.com/1063) and its [discussion thread](https://www.erdosproblems.com/forum/thread/1063). Direct retrieval during the original screening failed or returned HTTP 403. Visible search-index material attributed `k*lcm(2,…,k-1)` to Cambie (StijnC) on 2025-10-01. Including `1` leaves this least common multiple unchanged. The screening did not inspect all current forum comments.
- [Formal Conjectures at commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean) supplies the definition and alignment target. `Statement.lean` reproduces its `Erdos1063.n` definition and retains The Formal Conjectures Authors' Apache-2.0 attribution. Its unproved declarations are not imported.
- The problem bibliography identifies Erdős–Selfridge, Problem 6447, *American Mathematical Monthly* (1983), p. 710, and Monier's factorial bound in volume 92 (1985), pp. 435–436. Mathematical credit for the least-common-multiple bound remains with Cambie. This package implements the Lean proof separately using Mathlib.

The copied definition, original proof implementation, supporting evidence, and third-party source snapshots retain their respective attribution and applicable licenses. The public export must preserve the package's license files and source headers.

## Bounded prior-work screening

The original official-repository screening was recorded at 2026-09-16 16:01:32 UTC, and the external screening at 2026-09-16 16:02:19 UTC (2026-09-17 00:01–00:02 in Asia/Shanghai). The following are findings at those fixed revisions, not claims about every subsequent change. No complete public Lean proof of this exact target was located within the inspected scope. This does not establish global priority or the absence of unpublished work. Third-party projects were inspected but not rebuilt.

| Source and fixed revision | Finding |
| --- | --- |
| [Official PR #56](https://github.com/TheJustinSunPrize/awards/pull/56), head `40446d5328cd5b23d4f7ac0569931deca13b6bcd` | Open at inspection. All 22 changed files, the proof at the fixed head, and the PR body were read; comments, reviews, and inline threads were empty. It proves Monier's `n k ≤ k!`, a factorial witness, and threshold existence, and expressly excludes Cambie's stronger bound. This package does not import that proof. |
| [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean), `40e7c98697de6f66b8cbdbf641749ab39ed9c152` | Matching definition and target; `cambie_upper_bound` is still `sorry`. |
| [Paul-Lez/fc100](https://github.com/Paul-Lez/fc100/blob/4b48458754b42299b09af16590db56abe9ace268/FC100Solved/ErdosProblems/1063.lean), `4b48458754b42299b09af16590db56abe9ace268` | The same natural-number target is `by sorry`; the full tree and targeted searches did not locate another proof of 1063. |
| [rjwalters/lean-genius](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1063Problem.lean), `dc62f771ed5010abfdb04247dff6143e0e69d3e7` | `cambie_lcm_bound` is a custom axiom with right-hand side `k*(k-1)!`; its underlying definition allows at least `k-1` divisors. Small cases using `native_decide` do not prove this project's general target. |
| [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e), `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` | The complete, untruncated tree, `sources.yaml`, exact-symbol searches, and targeted searches did not locate the target. Numerous numeric-certificate hits for the broad string `1063` were not all exhausted. |
| [pw/erdos1063-upper-bound](https://github.com/pw/erdos1063-upper-bound/tree/a28481f5b4bda374086533397269c5b550c759b8), `a28481f5b4bda374086533397269c5b550c759b8` | The full tree contained documentation, logs, and Python checks, with no Lean files. Its asymptotic mathematical claims were not reviewed or used. |

Official-repository searches covered open and closed issue/PR titles, bodies, and comments with `JSP-000883`, `1063`, `Erdos1063`, `cambie_upper_bound`, `Cambie`, `lcm`, and `least common multiple`. The original grouped query counts were 0, 1, 4, and 1, all with `incomplete_results=false`; a page size of 100 returned every result. The only directly relevant item was #56; matches for #16, #22, #24, and #44 concerned other problems. Empty search results are evidence only within that search scope.

Pre-submission refresh: official repository searches at 2026-09-16 16:37:35 UTC, and PR #56 review checks at 16:43:14 UTC, found the same sole directly relevant PR and unchanged head. All search result sets were complete within the stated queries. Rules and terms were retrieved again and their visible text was unchanged. See [current-status.json](evidence/official/current-status.json).

## Submission rules and unresolved eligibility

The original screening read the [official rules](https://www.hejustinsun.com/zh/prize/rules), version 1.0 effective 2026-09-16, and [terms](https://www.hejustinsun.com/zh/prize/terms), updated the same day. Those texts address the 2026 contribution boundary, partial progress, the Lean formal-verifier role, verification, and priority. They do not specify a Lean/Mathlib version or decide this particular incremental formalization's eligibility. Eligibility, allocation, priority relative to #56, and acceptance of this toolchain remain organizer decisions.

At awards commit `f4e7173d89dfe91022a185427d63452c8ffbf6ae`, the [catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000883) was Progress / Lean proof No / Eligible to claim No. This package does not change those flags. The [PR template](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/.github/PULL_REQUEST_TEMPLATE.md) and [CONTRIBUTING](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/CONTRIBUTING.md) require English submission documentation, fixed evidence, attribution, and repository checks.

At the original inspection, `submissions/` was a community-proposed intake location rather than an established upstream proof-package format; [PR #13](https://github.com/TheJustinSunPrize/awards/pull/13) remained open without a public response. A submission under that directory is an intake proposal subject to maintainer direction. It does not create an official candidate, recipient, award, or claimed record.

The publishing account is [pcycho](https://github.com/pcycho). This is a public GitHub identity, not a verified award-recipient identity. The package was prepared with Codex assistance. The proposed intake PR supplies fixed source and evidence links and actual awards-repository checks. A versioned GitHub release is an external copy, not a permanent DOI archive; permanent archival remains pending. Private identity documents, private contacts, and payment information are outside this source package.

Final release verification: **e38f0a6fd3e344dfa4cc67d05e224346 / PASS**. See `logs/results.json` and `README.md` for the completed record. Public logs and environment-bearing evidence are explicitly redacted copies; original outputs remain local. The export rules and affected-file manifest accompany the public distribution in `logs/REDACTION.md` and `logs/redaction-manifest.json`. Hashes identify bytes and do not certify an execution independently. The verification uses pinned official dependency caches, does not rebuild all of Mathlib, and does not run another kernel implementation. It is distinct from organizer verification and an award decision.
