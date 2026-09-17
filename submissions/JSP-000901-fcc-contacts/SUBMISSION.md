# Submission evidence: JSP-000901

## Exact contribution

For every `m >= 0`, an explicit face-centred cubic box contains `4m^3`
points in `EuclideanSpace R (Fin 3)`, all distinct points at distance at
least one, with exactly `6m(2m-1)^2` unordered unit-distance contacts.

The package also proves that, for every `n >= 4`, there is an injectively
indexed configuration of exactly `n` separated points with at least
`6n - 200 n^(2/3)` unordered contacts. The constant 200 is explicit and
nonoptimal. Choose `m` with `4m^3 <= n < 4(m+1)^3`, then add
`n-4m^3` isolated points at distance at least two from each other and the box.

Contact graphs use actual Euclidean distance equal to one. The canonical
parity-class orientation is proved to be bijective onto their `Sym2` edge
sets, so contacts are neither omitted nor counted twice. The cardinality,
Euclidean separation, exact edge count, scale choice, and real-power bound
are all proved from source.

Key declarations: `FCC.point_separated`, `point_dist_eq_one_iff`,
`contactPairs_card`, `contactGraph_edge_card`,
`paddedContactGraph_edge_card`, `exact_contacts`,
`exact_padded_contacts`, and `all_cardinalities`.

## Mathematical provenance and scope

This formalizes the classical three-dimensional FCC construction and
the lower bound `f_3(n) >= 6n - O(n^(2/3))` associated with Erdos Problem
1084. It does not prove the universal three-dimensional upper bound or formalize
the planar contact-number formula. No mathematical novelty, optimal
constant, or global formalization priority is claimed.

The earlier [PR #275](https://github.com/TheJustinSunPrize/awards/pull/275)
explicitly submits the one-dimensional formula `f_1(n)=n-1` and excludes the
three-dimensional bounds. This package addresses the distinct three-dimensional
FCC lower-bound component, not that one-dimensional result. This scope
comparison is not an assertion that the wider novelty search is exhaustive.

At fixed commit `dc62f771ed5010abfdb04247dff6143e0e69d3e7`, the inspected
rjwalters/lean-genius file `Erdos1084OQ01.lean` declares its FCC lower bound
as `axiom fcc_cluster_pairs`. This package supplies a complete construction
with a related all-size lower bound, without importing that file or its
assumption. It is not a literal drop-in replacement: the external assertion
starts at `n >= 2` and uses a different configuration encoding. The source
comparison records those differences and the limits of the search.

See `PROOF.md` and `SOURCE_COMPARISON.md` for the proof and fixed-source details.

## Immutable published evidence

- Source: [156631890/fcc-contact-lower-bound](https://github.com/156631890/fcc-contact-lower-bound/tree/7f41967e7188f3cd08b5a3c4a14322c9175fca89).
- Fixed commit: `7f41967e7188f3cd08b5a3c4a14322c9175fca89`.
- [Release v1.0.0](https://github.com/156631890/fcc-contact-lower-bound/releases/tag/v1.0.0), release ID `390543373`.
- [Source and verification archive](https://github.com/156631890/fcc-contact-lower-bound/releases/download/v1.0.0/fcc-contact-lower-bound-v1.0.0.zip), asset ID `569816226`.
- Archive size: `36775` bytes.
- Archive SHA-256: `1170ec2de7dfe4b38cbc7aa87a859627eabdc3abdc2ad764266205224dba1758`.
- The uploaded archive was downloaded again and matched the fixed Git source
  and all `21` recorded source/configuration/document hashes.

## Local proof verification

Lean `4.33.1`, release commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
with Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`.

- `lake --wfail build FCC`: exit 0.
- `lake env lean -DwarningAsError=true Audit.lean`: exit 0;
  `20` audited declarations use only standard Lean axioms
  (`propext`, `Classical.choice`, and/or `Quot.sound`).
- `lake env leanchecker --verbose FCC` with `LEAN_NUM_THREADS=1`:
  exit 0; all `9` local proof modules replayed.
- Actual logs, pinned dependencies, reproduction script, and file hashes are
  included under the package directory. The separate source-level statement
  review is in `statement-review.md`.

Replay uses Lean's own kernel implementation and trusts imported package
artifacts. It is not an independently implemented checker, a fresh replay of
every imported dependency, or a network-isolated verification.

## Attribution and requested review

This is a self-submission by public account `156631890`, requesting review
of the precise formalization above and consideration for any applicable award
category. The proposed contribution recipient is `RECIPIENT-JSP-000901-A`;
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

Only `submissions/JSP-000901-fcc-contacts/` is added. The PR changes no catalog
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
