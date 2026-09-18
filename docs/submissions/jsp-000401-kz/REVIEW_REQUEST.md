# Review request: JSP-000401, classical 5/9 lower bound

Please review this partial Lean formalization contribution for JSP-000401. For every natural n, it constructs a finite simple three-uniform hypergraph on Fin n with no tetrahedron and with 5 * choose(n,3) <= 9 * |E|. This is the known Turán lower bound, not a solution of the open matching-upper-bound problem.

The implementation proves the all-n result by exact finite averaging over three-colorings. It includes permutation invariance, a kernel-reduced four-color-pattern obstruction, exact extension counts, and a direct finite-set statement of the forbidden subhypergraph. It does not depend on a finite search over graph orders or an unproved asymptotic assumption.

Mathematical credit: Paul Turán. The new Lean implementation uses Mathlib and OpenAI ChatGPT assistance under the submitting account's direction. Proposed recipient: RECIPIENT-JSP-000401-KZ-A, confirmation pending. This is a self-submission for assessment of the formalization contribution; no mathematical novelty, global first-formalization priority, or independent human review is claimed.

The official catalog remains Open / Lean No / Eligible No. Please assess whether this scoped contribution is substantive and eligible for any formalization pathway, and advise on the correct intake placement. No award record, candidate record, payout, recipient confirmation, or catalog status is changed.

Proof package at its tested commit:
https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/096288b2f397e11772e15deda80c3b277247b6e4/projects/jsp-000401

Public contributor-run verification:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176557771

See README.md for the mathematical argument and exact scope, and VERIFICATION.md for actual check outcomes. Cached Mathlib dependencies and network access are used; neither a full offline dependency rebuild nor organizer approval is claimed. GitHub Actions artifacts have finite retention. Source is preserved at immutable commits.
