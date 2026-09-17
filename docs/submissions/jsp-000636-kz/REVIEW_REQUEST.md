# Request for supporting-formalization review: JSP-000636

Please assess the scope, fidelity, attribution and eligibility of this
formalization of the universal upper bound in He and Tang's Lemma 2.5.
The theorem holds for every n >= 4 and r >= 2. Its original exact-multiplicity
form states that an antichain with exactly r members at every occurring
size has at most r(n-3) members.

The mathematical argument is known. The contribution offered here is the
Lean implementation, its explicit connection to Mathlib's antichain
predicate, and reproducible verification. This does not determine or
improve the threshold n₀(r), prove the paper's threshold estimates, or
resolve the complete original problem. Please determine whether this
limited supporting formalization qualifies for any recognition; no
completion category or award entitlement is presumed.

- Proposed recipient: `RECIPIENT-JSP-000636-KZ-A`; confirmation pending.
- Mathematical source: Yixin He and Quanyu Tang,
  [arXiv:2602.09803v1, Lemma 2.5](https://arxiv.org/html/2602.09803v1#S2).
- Assistance: OpenAI ChatGPT.
- [Pinned proof package](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/61368d8d5c75eb4854ba9c057933c20446f5d4cc/projects/jsp-000636).
- [Verification workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35172497300).
- Exact statements, definitions and bounded prior-art search: [README](README.md).
- Actual checks and their limits: [verification receipt](VERIFICATION.md).

The catalog currently records `Eligible to claim: No`. This package does
not override that record. It creates no candidate or award record and
does not claim first priority, independent human review, organizer
acceptance, or payment approval. Attribution to the mathematical authors
and to Mathlib remains explicit.
