# Submission evidence: JSP-000467

## Exact contribution

For every `a,b >= 0`, the maximum number of vertex-disjoint ordinary
four-cycles in the complete bipartite graph `K_(a,b)` is exactly
`min(floor(a/2), floor(b/2))`. The package proves both the upper bound for
arbitrary packings and an explicit attaining construction, including empty
parts and the zero-packing boundary.

For every `k >= 1`, `K_(2k-1,2k+1)` has `4k` vertices, minimum degree
`2k-1`, and maximum packing size `k-1`. Thus the degree threshold `2k`
in Wang's theorem cannot be decreased, even for arbitrarily large graphs.

The graph is Mathlib's `completeBipartiteGraph`. A packing is a single
injection from `Fin k x Fin 4` preserving the adjacency of `cycleGraph 4`;
this expresses vertex-disjoint ordinary cycles. Chords are permitted.
Key declarations in namespace `BipartiteC4` include `hasPacking_iff`,
`exact_capacity`, `maximum_attained`, `sharpness`,
`necessary_degree_threshold`, and `arbitrarily_large_sharpness`.

## Mathematical provenance and scope

This is a precise sharpness component associated with Erdos Problem 577,
not a new proof of Wang's sufficient-degree theorem or a new solution of the
complete catalog problem. The bipartite construction is classical, and no
new mathematics or global formalization priority is claimed.
The bounded source comparison inspected the original problem page and
selected files of plby/lean-proofs at a fixed commit. It did not review every
supporting module and cannot exclude equivalent formalizations elsewhere.

Pre-submission update (September 17, 2026): the current search found
[recipient recommendation #591](https://github.com/TheJustinSunPrize/awards/issues/591)
and [PR #595](https://github.com/TheJustinSunPrize/awards/pull/595), submitted by
public account `renzhonghua8`. Their actual descriptions restrict the result to
the positive `k = 1` case: every four-vertex graph of minimum degree at least two
contains a four-cycle. This package instead proves the exact capacity of every
complete bipartite graph and the necessary-degree obstruction for every `k >= 1`.
These are different scoped components; neither description claims Wang's full
positive theorem. This comparison is based on the prior PR description at head
`cfd4d20271220c2de718bda849d0ad0f0c0e4934`, not an independent audit of that proof.
The no-match search recorded in the immutable source archive predates these
submissions and is not presented as the current search result.

See `PROOF.md` and `SOURCE_COMPARISON.md` for the proof and fixed-source details.

## Immutable published evidence

- Source: [156631890/bipartite-c4-packing](https://github.com/156631890/bipartite-c4-packing/tree/b0ac7cc3d39b82e77ce8ef436871d24381c194f5).
- Fixed commit: `b0ac7cc3d39b82e77ce8ef436871d24381c194f5`.
- [Release v1.0.0](https://github.com/156631890/bipartite-c4-packing/releases/tag/v1.0.0), release ID `390537565`.
- [Source and verification archive](https://github.com/156631890/bipartite-c4-packing/releases/download/v1.0.0/bipartite-c4-v1.0.0.zip), asset ID `569799752`.
- Archive size: `26239` bytes.
- Archive SHA-256: `1807d65ad5bdb20d95d45fa2b017c9f797f1fe30844e5e8b6e2f26c2aff81748`.
- The uploaded archive was downloaded again and matched the fixed Git source
  and all `18` recorded source/configuration/document hashes.

## Local proof verification

Lean `4.33.1`, release commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
with Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.

- `lake --wfail build BipartiteC4`: exit 0.
- `lake env lean -DwarningAsError=true Audit.lean`: exit 0;
  `14` audited declarations use only standard Lean axioms
  (`propext`, `Classical.choice`, and/or `Quot.sound`).
- `lake env leanchecker --verbose BipartiteC4` with `LEAN_NUM_THREADS=1`:
  exit 0; all `5` local proof modules replayed.
- Actual logs, pinned dependencies, reproduction script, and file hashes are
  included under the package directory. The separate source-level statement
  review is in `statement-review.md`.

Replay uses Lean's own kernel implementation and trusts imported package
artifacts. It is not an independently implemented checker, a fresh replay of
every imported dependency, or a network-isolated verification.

## Attribution and requested review

This is a self-submission by public account `156631890`, requesting review
of the precise formalization above and consideration for any applicable award
category. The proposed contribution recipient is `RECIPIENT-JSP-000467-A`;
recipient identity confirmation remains pending.

Proof development, exposition, local checking and a separate source-level
review used OpenAI Codex and collaborating agents. The review is AI
collaboration, not external specialist review or independent kernel validation.
The package retains mathematical attribution and an Apache-2.0 source license.

In the problem index (`problems/README.md`) at fixed base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`, this entry is marked
`Eligible to claim: No` and `Claim status: Unavailable`. This submission does
not assert existing eligibility or entitlement to payment. It requests an
assessment of the evidenced contribution. No organizer affiliation, committee
conclusion, official verification status, priority determination, award or
payment authorization is claimed.

Only `submissions/JSP-000467-bipartite-c4/` is added. The PR changes no catalog
flag, candidate or award record, recipient profile, or published decision.
No private contact information, identity documents or payment data are included.


This directory is a proposed review-evidence location, not a formal candidate
record. Maintainers may request relocation or external-evidence links only.
The complete source and verification archive is already externally published.

The [first-batch announcement](https://x.com/sunyuchentron/status/2100497325416460762)
was checked on September 17, 2026. This is a later evidence submission, not a
claim to an already announced award. Under the currently published
[v1.0 rules](https://www.hejustinsun.com/zh/prize/rules), completion, first
contribution and eligibility still require assessment. Please clarify whether
this new formalization of a classical component can enter any subsequent
evaluation; no next-batch schedule or acceptance is assumed.

Review and any applicable eligibility decision remain pending. The repository's
CI validates records and links; it does not execute these Lean proofs or decide
awards. No synthetic reviewer or candidate record has been created.
