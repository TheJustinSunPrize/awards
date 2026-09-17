# External work and statement comparison

Reviewed on 2026-09-17. This note supplements the original bounded issue search; an empty search result is not evidence that no public formalization exists.

## Relevant public source

The public repository `plby/lean-proofs` contains [Erdos877.lean at commit 33a6b9a285cb64ac276ce4d0b3a4111b82c972b6](https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos877.lean). GitHub records this commit on 2026-08-23, before this submission. The fetched file has Git blob SHA `95c2b10d5fd8004181b7ed496918e75d3cfe47db`.

Its header credits informal mathematics to Balogh, Liu, Sharifzadeh and Treglown, and formal work to Codex and GPT-5.6 Sol. Those are the upstream file's attributions, not a claim of authorship by this submitting account.

The source declares `Erdos877.erdos_877`, with conclusion that the number of inclusion-maximal sum-free subsets of `{1,...,n}` is `o(2^(n/2))`. It also declares `Erdos877.erdos_877_exponential_bound`, giving an eventual bound `2^(c*n)` for a defined constant `c < 1/2`. The definitions use inclusion maximality and allow the summands in a forbidden sum to coincide, matching the finite objects in this submission.

## Distinct scopes

| Work | Statement | Review status in this package |
| --- | --- | --- |
| Included `JSP000728.cameron_erdos_lower_bound` | For every natural `n`, the count is at least `2^(n/4)` with natural-number division. | Compiled and independently checked as recorded in VERIFICATION.md. |
| Public `Erdos877.erdos_877` | The count is `o(2^(n/2))`. | Source and declarations inspected; the external project and its transitive dependencies were not independently rebuilt or checked in this review. |
| Balogh–Liu–Sharifzadeh–Treglown, [arXiv:1409.5661](https://arxiv.org/abs/1409.5661) | Upper bound `2^((1/4+o(1))*n)`, matching the classical lower bound at exponential scale. | Published mathematical result, outside the included Lean proof. |

The external upper-bound declarations do not themselves establish that this particular lower-bound theorem was previously formalized. Conversely, the lower-bound proof here does not supply any of the upper bounds. Combining the submitted lower bound with the external `c < 1/2` bound would still not establish the sharp exponent `1/4`.

The submission therefore remains a scoped formalization of a known lower bound. It is not a first formal solution of the catalog question, does not claim ownership of the external work, and does not establish award eligibility. The catalog's `Lean proof: No` label must not be used as a substitute for an external priority search.

## Submission state checked

[Official PR #373](https://github.com/TheJustinSunPrize/awards/pull/373) was open at this review, with no posted reviews or discussion comments returned by the GitHub API. No organizer acceptance or award decision was observed. This is a dated observation, not a promise about future review or payment.
