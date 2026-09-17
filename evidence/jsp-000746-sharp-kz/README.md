# JSP-000746: sharpness-supplement contribution proposed for review

## Related entry and recipient confirmation

Related problem: **JSP-000746 / Erdos Problem 895**. Existing upper-bound evidence is discussed in [issue #19](https://github.com/TheJustinSunPrize/awards/issues/19).

Proposed recipient placeholder: **RECIPIENT-JSP-000746-A**. Confirmation status: **pending**. No unconfirmed legal identity, private contact, confirmation document, or payment information is supplied.

This is a self-interested recommendation of the submitting account's AI-assisted incremental formalization contribution. Whether that contribution is substantial or otherwise eligible for prize recognition remains for reviewers. This document does not change catalog eligibility, recipient records, verification status, or award records.

## Exact contribution and limitations

Let P(n) mean that every triangle-free simple graph on labeled vertices `{1,...,n}` contains distinct pairwise nonadjacent vertices `a,b,a+b`, with `a<b`. The new Lean code proves **P(n) if and only if n >= 18**, for every natural n including zero.

The added formal content is an explicit 43-edge graph on 17 vertices, its triangle-freeness and absence of an independent distinct-summand Schur triple, the restriction argument for every `n <= 17`, and the exact-threshold equivalence using the unchanged existing upper-bound proof.

This is **not a claim of new mathematics or the first formalization of the original problem**. The stronger Hindman-set question is not claimed. The finite threshold theorem implies the original existence assertion on the integers by restriction to positive labels 1,...,18, but no separately named integer-graph Lean corollary is added.

## Attribution and relationship to prior work

The mathematical upper-bound result is credited to **Ben Barber**, consistently with the official catalog and source. The reused formal upper-bound source in `plby/lean-proofs` credits **Codex and GPT-5.6 Sol**. It and its certificates are pinned to commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` and imported unchanged.

Issue #19 already reports successful verification of the sufficient bound 18 and explicitly excludes a sharpness claim. The existing source calls the threshold sharp in prose, but its Lean declarations provide the sufficient upper bound rather than the 17-vertex witness and exact-threshold equivalence supplied here. This supplement does not reassign authorship of that proof or claim the earlier reviewer's reproduction work. Wider overlap, priority, and significance review is requested.

The new witness/formal restriction/threshold code, independent finite checkers, and reproduction record were prepared with **OpenAI ChatGPT assistance** for the submitting account. The witness was found independently by integer feasibility search; the search solver is not trusted by the formal proof. No exclusive priority or specified award allocation is asserted.

## Immutable source and successful Lean evidence

- [Pinned new proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b62eb3c313e08907fc76fe927cf28545a38178e0/projects/jsp-000746-sharp/JSP000746Sharp.lean)
- Proof commit: `b62eb3c313e08907fc76fe927cf28545a38178e0`
- New source SHA-256: `8f3ffdbdc222b94abe89e74413833f011880651136767e8b8cc3fe90190803b2`
- [Successful workflow run #4](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172135809), completed September 17, 2026 UTC / September 16, 2026 America/New_York
- [Evidence artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172135809/artifacts/10476738843), ID `10476738843`
- Artifact ZIP SHA-256: `e8931676c8664efe515edab27190b5f92f706af6bbafa1b9116650914194099f`
- Lean `4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`
- [Pinned reproduction record and independent checkers](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/123fa30f98f8d759e0670c791ff47f5579a7ce2b/evidence/jsp-000746-sharp)

Both the unchanged upper-bound module and the new module compile with `-DwarningAsError=true`. All seven audited new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`, `Lean.ofReduceBool`, or added mathematical axiom. Finite checks use `decide`, not `native_decide`.

The audited declarations in namespace `JSP000746Sharp` are `no_triangles`, `schur_coverage`, `witness_triangle_free`, `witness_no_independent_schur_triple`, `counterexamples_below_eighteen`, `exact_threshold`, and `least_threshold`.

Both `leanchecker --verbose Erdos895` and `leanchecker --verbose JSP000746Sharp` completed successfully. A separate module importing the result and trying to prove `(2 : Nat) + 2 = 5` by `decide` was rejected as false. The artifact was downloaded, its file-manifest hashes checked, and the compiled source compared byte for byte with the published source. Earlier failed development runs are disclosed in the reproduction record and are not offered as successful evidence.

## Independently executed finite checks

The standard-library Python witness checker compares its edge list with the Lean source and checks all **680** unordered triples, all **64** distinct-summand Schur triples on 17 vertices, and every restriction `n=0,...,17`. Deliberately introducing a triangle or deleting an essential covering edge is detected.

A separate RUP checker reconstructs the exact 18-vertex graph encoding: **153 variables, 816 triangle clauses, and 72 Schur clauses**. It verifies the pinned LRAT trace's **2,076 RUP additions, 747 deletions, and 33,999 unit/conflict hints**, deriving the empty clause. It rejects unsupported RAT hints, removal of final proof hints, and a corrupted graph encoding.

These Python checks were executed separately from Lean CI. They are independent finite verification software, **not an independently implemented Lean kernel**. `leanchecker` is a replay with Lean's kernel, not a second kernel implementation. Human statement and attribution review remain necessary.

## Requested review

Please assess only the added sharpness formalization, finite certificate checks, and reproduction work, preserving existing mathematical and formalization credit and linking this supplement with issue #19. This is evidence for contribution review, **not a completed official verification record, a confirmed recipient identity, an award announcement, or an entitlement to payment**. No prior solution or award allocation is disputed.
