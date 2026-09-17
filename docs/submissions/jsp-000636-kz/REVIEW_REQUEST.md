# Request for expanded formalization review: JSP-000636

Please assess this supplement in the existing
[PR #382](https://github.com/TheJustinSunPrize/awards/pull/382).
The original packet proved the universal antichain upper bound. This
version also includes the critical threshold lower bound, a general
attaining construction, threshold existence, and exact-multiplicity
thinning. No new candidate or award record is being created.

The principal statements are:

- For every r >= 4, g(2r+2,r) <= 2r-2, hence every threshold is >= 2r+2.
- For every r >= 2 and n >= 2r+4 floor(sqrt r)+8, an antichain with exactly
  r sets at each of n-3 occurring sizes exists, with r(n-3) total sets.
- For every r >= 2 the least eventual-equality threshold exists.
- For every r >= 4, 2r+2 <= n0(r) <= 2r+4 floor(sqrt r)+7.

The quantifiers are unrestricted apart from these hypotheses; this is
not a finite list of checked instances. The finite extremal maximum
ranges over all admissible families. Threshold existence is proved
before using a least-threshold definition. Positive-r levelwise thinning
formally connects the at-least-r and exactly-r conventions.

This implements known mathematics and a pair-label specialization of
He–Tang's section 4 construction, with mathematical attribution retained.
The O(sqrt r) upper error does not formalize the paper's sharper
O(log r) estimate. Exact small-r thresholds and a full determination of
n0(r) remain outside the proved scope. Please assess this partial
formalization contribution on that basis; no full-solution category,
priority, award eligibility or payment entitlement is presumed.

- Proposed recipient: `RECIPIENT-JSP-000636-KZ-A`; confirmation pending.
- Mathematical source: Yixin He and Quanyu Tang,
  [arXiv:2602.09803v1](https://arxiv.org/html/2602.09803v1), Lemma 2.5,
  the lower estimate in Theorem 1.4, and the section 4 construction.
- Assistance: OpenAI ChatGPT.
- [Pinned expanded proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/d5fc3ee7fc5a452e8104b5099c854a5a15a668bf/projects/jsp-000636).
- [Expanded CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177799617).
- [Definitions and proof outline](README.md).
- [Actual verification results and limits](VERIFICATION.md).
- [Retained earlier evidence](upper-only-VERIFICATION.md).

The catalog currently records `Eligible to claim: No`. This packet
requests review and does not change that flag or claim organizer
acceptance. Source is Apache-2.0; documentation is CC BY 4.0.
