This PR requests review of the classical finite-field incidence **lower-bound formalization** for JSP-000463 / Erdős Problem 573.

For every finite field of cardinality q, the package constructs a simple graph with exactly 2q² vertices and q³ edges, and proves that it contains neither a triangle nor a 4-cycle. It proves q³ ≤ ex(2q²; {C3,C4}), specializes to every prime q, and proves the existence of arbitrarily large graph orders with the exact identity 8e²=n³.

The supplement `AllOrders.lean` also proves a graph-existence theorem and the uniform bound **n³ < 512 exC3C4(n)² for every n ≥ 8**, using Bertrand's postulate and padding by isolated vertices. It includes a proof that exC3C4 is monotone. The uniform constant is eight times smaller than the conjectured sharp constant.

This is **partial scope** relative to the conjecture ex(n; {C3,C4}) ~ (n/2)^(3/2). It does not establish the matching upper bound or the all-order asymptotic. The construction is classical mathematics; no mathematical novelty or global first-formalization priority is claimed.

Prior work: [PR #313](https://github.com/TheJustinSunPrize/awards/pull/313) and [Issue #314](https://github.com/TheJustinSunPrize/awards/issues/314) already formalize an upper bound and explicitly leave the lower construction unformalized. This submission contributes the complementary construction and does not import that upper-bound code. Credit to baobingzhang, the classical mathematical authors, and Mathlib is retained in README.md.

The complete package is under `docs/submissions/jsp-000463-kz/`. It includes actual Lean proofs, pinned dependencies, reproduction scripts, statement correspondence, prior-work comparison and verification records. No existing catalog, candidate, award or recipient-confirmation record is changed.

- [Immutable proof source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/91a57fa9ab5d0f0f1df3f94e156e29fc4a8ca0f2/projects/jsp-000463)
- [Public verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177883810)

The fixed extended revision passed public Lean compilation, kernel replay, all 18 target axiom audits, nine dependency pin checks and negative controls. NaNoda independently checked 32,138 declarations with no errors. Verification details and artifact retention are recorded in VERIFICATION.md. The original construction and its successful verification are preserved in Git history. Contributor-run checks do not constitute official approval or independent human review.

Submitting account: `ketianzhang1-lang`; proposed recipient placeholder: `RECIPIENT-JSP-000463-KZ-A`, confirmation pending. Prepared with OpenAI ChatGPT assistance. This is a self-submission. Please assess statement fidelity, attribution, overlap, reproducibility and whether the contribution qualifies under the published rules for partial formalization progress. No award or payment entitlement is asserted.
