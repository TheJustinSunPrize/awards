# JSP-000212: prime-power Bose--Chowla formalization

## Requested review and current scope

Please assess this supplement to [PR #423](https://github.com/TheJustinSunPrize/awards/pull/423).
It extends the initial prime-cardinality construction to **every prime
power and modular equality of sums**, completing the finite Bose--Chowla
construction. This is one contribution in the existing PR, not a second
award application.

The original [JSP-000212 extremal problem](../../../problems/catalog-0201-0300.md#JSP-000212)
remains open. This is the formalization of a known lower-bound construction;
it claims no new bound or mathematical discovery, complete solution of the
extremal question, worldwide priority, or prize entitlement.

The proposed recipient is `RECIPIENT-JSP-000212-KZ-A`, confirmation pending.
This self-submission by `ketianzhang1-lang` was prepared with OpenAI ChatGPT
assistance. The submitter has a direct interest in the review outcome.
Mathematical credit remains with R. C. Bose and S. Chowla.

## Exact theorem

For every prime p, every r >= 1 and h >= 2, write q=p^r. There exists a set
A in {1,...,q^h-1} of cardinality q such that **congruent sums modulo q^h-1
of h elements of A have the same multiset of summands**, including repetitions.

The final theorem is `BoseChowlaPrimePower.exists_prime_power_modular`.
It proves the existence of the finite-field embedding and the required
extension degree, without extra conjectural assumptions.
`BoseChowlaPrimePower.jsp000212_prime_power` specializes to h=3 and the
catalog's sums of distinct three-element subsets.

| Feature | Initial submission | Current supplement |
| --- | --- | --- |
| Cardinalities | Primes p | All prime powers q=p^r, r >= 1 |
| Sum comparison | Equality in the integers | Congruence modulo q^h-1 |
| Number of summands | Every h >= 2 | Every h >= 2 |
| Repeated summands | Allowed | Allowed |
| JSP-000212 endpoint | At N=p^3-1, size p | At N=q^3-1, size q |
| Complete original extremal problem | Not claimed | Not claimed |

## Source and evidence

- [Immutable current proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/9ef8a063998150500dcdddad81c669c69ed8fa2c/projects/jsp-000212).
- [Current verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178083844).
- [Proof, attribution and reproduction](PROOF.md).
- [Current verification receipt](VERIFICATION.md).
- [Source checksums](SOURCE_SHA256SUMS).
- [Historical initial receipt](INITIAL_VERIFICATION.md).
- [Initial submission snapshot](https://github.com/ketianzhang1-lang/awards/tree/546e5b052fef4a87a0853501c46ed36df2eed402/docs/submissions/jsp-000212-kz).
- [Suggested updated PR description](PR_DESCRIPTION.md).

BoseChowla.lean and Audit.lean are byte-identical to the initial verified
version. The new PrimePower.lean and PrimePowerAudit.lean supply the
supplement. Documentation and verification scripts now cover both.
The old run, source pin and evidence remain traceable; the initial date
does not establish priority for the later extension.

The proof uses Mathlib and standard foundational axioms. No unproved
conjecture, custom target assumption, native-evaluation axiom or sorry is
used. Source and scripts are Apache-2.0. Relevant mathematical attribution
is retained in PROOF.md.

Bounded official issue/PR and public-source searches found no separate
matching submission on 2026-09-17; they do not prove global novelty.
Catalog flags, public candidate records and award records remain unchanged.
Contributor-run checks do not replace designated verification, human
statement review, recipient confirmation, priority or eligibility decisions.
