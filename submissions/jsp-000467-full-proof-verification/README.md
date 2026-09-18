# JSP-000467 / Erdős 577: existing full-proof verification and statement bridge

This note supersedes the earlier contribution description for review
purposes. The [historical base-case package](../jsp-000467-renzhonghua8-k1/README.md)
remains unchanged except for a scope-correction notice. It proves `k = 1`
only and is not a dependency of the full proof reviewed here.

**New verification status: passed.** The new run freshly compiled the complete
851-module proof-source closure and bridge, directly audited the requested
theorem bodies, and completed the full imported-environment kernel replay.
No historical base-case result is used as evidence for this reproduction.

## Complete statement and contribution

For every natural `k`, every finite simple graph with `4k` vertices and
minimum degree at least `2k` has `k` pairwise vertex-disjoint ordinary
four-cycles covering all vertices. The statement includes every `k ≥ 2`
and the boundary degree. Chords are allowed.

The new work is an independent Mathlib statement, a bridge from the existing
complete theorem, and source/statement review and reproduction tooling.
The conclusion uses standard `cycleGraph 4` copies, vertex-disjointness,
and full coverage. It is not a new proof of the graph-theoretic theorem or
a first formalization.

## Source and attribution

- Mathematical theorem: Hong Wang (2010),
  [*Proof of the Erdős–Faudree Conjecture on Quadrilaterals*](https://doi.org/10.1007/s00373-010-0948-3),
  Theorem B.
- Existing complete Lean development: Boris Alexeev's
  [`plby/lean-proofs`](https://github.com/plby/lean-proofs), retaining its
  contributor acknowledgments.
- Original main-proof addition:
  [`5e2819485d58d9d5cb0f2d7638c8dafc07535332`](https://github.com/plby/lean-proofs/commit/5e2819485d58d9d5cb0f2d7638c8dafc07535332),
  dated 2026-08-28.
- Reviewed upstream commit:
  [`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
- Main upstream source: `src/latest/ErdosProblems/Erdos577.lean`, endpoint
  `Erdos577.erdos_577`.
- New contribution:
  [verification repository](https://github.com/renzhonghua8/jsp-000467-full-proof-verification),
  checked commit `90eb2ad461ee23d9843b8972fc4a48ac9e566f62`;
  release/documentation commit `36065b87605bcea2131803b4fa3ea5b96ba7be05`.

Our earlier search failed to locate this prior full development. This note
corrects that omission. The new package fetches upstream code unchanged for
local verification; it does not redistribute or relicense the proof sources.

## Evidence index

| Evidence | Current status and exact record |
| --- | --- |
| Environment | Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` |
| Transitive source audit | Pass: 851 proof modules, no missing/cyclic local imports or forbidden tokens; SHA-256 `b0b0fbbcbfd9255683e3b68b144374e4ade5900b1d27c6f08bfc7e1ce438a5b2` |
| Full project proof-source rebuild and bridge compilation | Pass: all 851 expected modules freshly built once; bridge built; exit status 0; complete log SHA-256 `1310b30b4309d33a36a6e574dd08757f758259d8ad93b0a8ffc699a5922e05c7` |
| New CI | [Run 35226375007, attempt 1](https://github.com/renzhonghua8/jsp-000467-full-proof-verification/actions/runs/35226375007), head `90eb2ad461ee23d9843b8972fc4a48ac9e566f62`, `success` |
| Upstream and bridge endpoint axiom reports | [Summary](https://github.com/renzhonghua8/jsp-000467-full-proof-verification/blob/36065b87605bcea2131803b4fa3ea5b96ba7be05/verification/cloud-run-35226375007-summary.json): exactly `propext`, `Classical.choice`, `Quot.sound` for each target; no disallowed axiom |
| Additional kernel replay and imported-environment boundary | Pass: `leanchecker --fresh --verbose Jsp467FullReview.Bridge`; all loaded transitive imports replayed into an empty Lean 4.33.0 environment; exit status 0 |
| Archive ID, URL, SHA-256, byte count | Release `v1.0.0`, [asset](https://github.com/renzhonghua8/jsp-000467-full-proof-verification/releases/download/v1.0.0/jsp-000467-full-proof-verification-evidence-v1.0.0.tar.gz) ID `571758809`; `85921e9051778d4a512a29fa840e029eaf946b0413d12c1c940fe133e9c7bfed`; 152,430 bytes |

Matching compiled Mathlib caches may be used. A full project proof-source
rebuild is not a source rebuild of Lean or Mathlib. Reproduction performed
by the submitting account is not official independent Prize verification.

## Review scope

Related [PR #595](https://github.com/TheJustinSunPrize/awards/pull/595) and
[issue #591](https://github.com/TheJustinSunPrize/awards/issues/591).
Any attribution consideration for `RECIPIENT-JSP-000467-A` is limited to the
new statement bridge, review, and verification tooling/evidence. No
first-formalization priority, tier, award eligibility, or payment is claimed.
This submission note does not alter official problem or award records.
