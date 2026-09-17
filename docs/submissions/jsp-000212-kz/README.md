# JSP-000212: finite Bose--Chowla construction

## Requested review

Please assess this Lean formalization of a known lower-bound construction
for [JSP-000212](../../../problems/catalog-0201-0300.md#JSP-000212).
The original extremal problem remains open. This submission claims neither
a new mathematical result nor the first worldwide formalization. It requests
review of the formalization contribution, its scope, reproducibility, overlap,
and eligibility under the published prize rules.

The proposed recipient is `RECIPIENT-JSP-000212-KZ-A`, confirmation pending.
This is a self-submission by `ketianzhang1-lang`, prepared with OpenAI ChatGPT
assistance. The submitter has a direct interest in the review outcome.
Mathematical credit remains with R. C. Bose and S. Chowla.

## Exact contribution

For every prime `p` and every natural `h >= 2`, the package proves that there
exists `A ⊆ {1,...,p^h-1}` with exactly `p` elements such that equal sums of
`h` elements of `A`, **including repetitions**, have equal multisets of
summands. The main construction is `BoseChowla.exists_bose_chowla`.

`BoseChowla.jsp000212` specializes to `h=3` and transfers the result to sums
over three-element finite subsets, which is the exact condition in the
official catalog. In particular, at interval lengths `N=p^3-1` the relevant
maximum is at least `p`. The theorem covers every prime, not a fixed list.

| Catalog feature | Formal statement |
| --- | --- |
| Positive integer interval | `A ⊆ Finset.Icc 1 (p^3-1)` |
| Constructed size | `A.card = p` |
| Two three-element subsets | `S ⊆ A`, `T ⊆ A`, `S.card = 3`, `T.card = 3` |
| Equality only for the same subset | `S.sum id = T.sum id → S = T` |
| Known component only | No upper bound or complete asymptotic answer is asserted |

Only prime cardinalities are proved here; the classical theorem also covers
prime powers and a stronger modular condition. Neither additional scope is
silently claimed. The general `h` statement and cubic specialization are one
contribution, not separate award requests.

## Evidence and attribution

- [Immutable tested proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0/projects/jsp-000212).
- [Public proof verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176592120).
- [Proof explanation, original sources, and reproduction commands](PROOF.md).
- [Verification receipt and limitations](VERIFICATION.md).
- [Source file hashes](SOURCE_SHA256SUMS).

The proof uses only Mathlib; it does not import an unproved conjecture library
or add assumptions encoding the desired result. The original implementation
and verification scripts are Apache-2.0. Mathematical attribution and source
links are retained in PROOF.md.

Bounded official issue/PR and public-source searches found no matching
submission on 2026-09-17. They are not a proof of global novelty or priority.
The catalog's current Open / Lean No / Eligible No markers, public candidate
records, and award records are not modified. Automated checks are contributor
evidence; designated verification, human statement review, recipient
confirmation, priority, eligibility, and award decisions remain pending.
