# JSP-000465: supplementary formal verification evidence

Please review a compatibility port, exact problem interface, and reproduction
package for the already published connected-bipartite non-forest compactness
counterexample for JSP-000465 / Erdős 575.

**This is not a new mathematical solution or the first Lean formalization.**
The OpenAI team / Astra retains credit for the counterexample and the substantive
proof. The source registration in official PR #40 predates this package and is
explicitly acknowledged. The proposed incremental contribution consists of
Lean 4.34 compatibility fixes, the dedicated problem interface, a simultaneous
separation corollary, checks that the extrema are attained, and additional
reproduction evidence. Please determine whether this incremental contribution
merits recognition; no prize entitlement is asserted.

## Full statement coverage

There is a fixed nonempty finite family F of connected bipartite finite simple
graphs, all containing cycles, such that, for every K > 0, eventually for every
natural n and simultaneously for every H in F,

    K * ex(n,F) < ex(n,H).

The family extremal number uses ordinary subgraph containment. Every maximum is
attained by an actual family-free graph at each order. Its singleton case agrees
with Mathlib's usual extremal number. The package negates the universal
constant-factor compactness statement for families containing a bipartite member,
while explicitly retaining the stronger connected and non-forest conditions in
the witness theorem.

- [Statement comparison and derivation](proof/STATEMENT_REVIEW.md).
- [New interface source](proof/JSP000465.lean).
- [Attribution, earlier work, and reproduction commands](proof/README.md).
- [Compatibility changes only](proof/PORT.patch).
- [Verification record](VERIFICATION.md).
- [Review request](REVIEW_REQUEST.md).

The proof source is pinned at
[6a793b157c1afdf29f3e6bbbf3cf514535d1dfca](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/6a793b157c1afdf29f3e6bbbf3cf514535d1dfca/projects/jsp-000465).
The copied project files are byte-identical to that source; see
[PROOF_SHA256SUMS](PROOF_SHA256SUMS).

## Prior filings and contribution attribution

[PR #40](https://github.com/TheJustinSunPrize/awards/pull/40) registers the
existing full OpenAI proof. Its stated checks do not independently rebuild or
kernel-replay the third-party source. This package supplements that evidence;
it does not replace its authorship or priority.

[PR #401](https://github.com/TheJustinSunPrize/awards/pull/401) formalizes the
unrestricted forest example, which has a disconnected member. Its work is
acknowledged; this package retains the connected-bipartite, cyclic restriction.

The mathematical and upstream formalization credits are listed in the preserved
source headers and [proof README](proof/README.md). New port, interface, and
verification work was prepared under account `ketianzhang1-lang`, with OpenAI
ChatGPT/Codex assistance. Proposed contributor: `RECIPIENT-JSP-000465-KZ-A`,
confirmation pending. This is a self-submission for contribution review.

No catalog screening flag, candidate, recipient profile, award, or payment
record is changed. Machine checks do not replace independent human review of
statement fidelity, originality of contribution, overlap, attribution, or
eligibility. No independent permanent archive is claimed.
