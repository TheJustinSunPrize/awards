# Contribution recommendation: JSP-000897

## Related entry and proposed recipient

JSP-000897 / Erdos Problem 1079. Proposed placeholder: RECIPIENT-JSP-000897-KZ-A. Identity confirmation remains pending; no public written-confirmation attestation is supplied.

## Requested review

Please assess the submitting account's Mathlib 4.34.0 port, explicit integral-surplus supplement, and reproducibility evidence. The complete classical proof is included with prior attribution. A complete earlier Lean proof already exists, so this is an incremental formalization recommendation rather than an original-solver or first-formalizer nomination.

For r >= 4 and n >= 2, every n-vertex simple graph G satisfying e(G) >= ex(n,K_r) has a maximum-degree vertex v with n <= 2*d(v) and

ex(d(v),K_(r-1)) + e(G) - ex(n,K_r) <= e(N(v)).

The formal expression uses a parenthesized natural-number surplus, e(G)-ex(n,K_r), under its nonnegativity hypothesis. The surplus inequality also holds at every maximum-degree vertex. The retained complete non-strict and strict classical endpoints cover the threshold question in the cited formal specification.

## Public evidence

- Tested source: https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/914c6fa28200985d6409b5b34588b9f5c4a87d00/projects/jsp-000897
- CI: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35178602861
- Actual check outcomes and evidence retention: [VERIFICATION.md](VERIFICATION.md).
- Original and new contributions: [PROVENANCE.md](PROVENANCE.md).
- Scope and reproduction: [README.md](README.md).

## Attribution and limitations

Mathematics: Bollobas and Thomason; strict strengthening: Bondy. The earlier complete formalization is from plby/lean-proofs, explicitly credited in its source to Codex and GPT-5.6 Sol. Mathlib supplies the foundational graph and extremal-number library. Their work is not claimed by the submitting account. The port, supplement and review package were prepared with OpenAI ChatGPT assistance.

The exact public problem-page text could not be newly fetched (HTTP 403). Statement comparison used the immutable formal proof and official catalog. Reviewers should confirm correspondence with the original problem before awarding any credit.

No mathematical novelty, first-formalization priority, independent human sign-off, organizer approval, award allocation or payment entitlement is claimed. The catalog remains Solved / Lean No / Eligible No until organizers assess the evidence. Only this evidence directory is proposed; no candidate, award, recipient-confirmation or catalog record is modified.
