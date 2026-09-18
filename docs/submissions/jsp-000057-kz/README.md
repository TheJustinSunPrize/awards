# JSP-000057: exact f(2,3) = 7 (scoped classical case)

This contributor-prepared package requests review of a **classical special-case
formalization**, not closure of JSP-000057 / Erdős problem 20. The checked
statement is

```lean
JSP000057.f_two_three : Erdos20.f 2 3 = 7
```

Every family of at least seven distinct two-element sets contains a
three-petal sunflower. The six edges of two disjoint triangles show that
seven is the least such number. The code proves both directions and connects
them to the original `Set (Set α)` threshold definition, uniformly over all
ground types. No added combinatorial hypothesis is assumed.

**The general sunflower conjecture remains unresolved by this work.** This
is not a new mathematical bound and does not claim first formalization.
The existing general Erdős–Rado bound formalization is acknowledged in
[PROVENANCE.md](source/PROVENANCE.md).

## Evidence and reproduction

- [Complete Lean project](source/README.md)
- [Exact correspondence with the original definitions](source/STATEMENT.md)
- [Verification report](VERIFICATION.md)
- [Contributor verification workflow](workflow/jsp-000057.yml)
- [File hashes](SHA256SUMS)

Pinned proof commit:
[`b45035ab53aece620f2029e0e73c7e8146718cd1`](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/b45035ab53aece620f2029e0e73c7e8146718cd1/projects/jsp-000057).
Contributor workflow:
[run 35177146542](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177146542).
The report records the observed outcome and what each check establishes.
From `source/`:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

## Requested review and attribution

Recipient placeholder: `RECIPIENT-JSP-000057-KZ-A`; identity confirmation is
pending. This is a self-submission prepared with OpenAI ChatGPT / Codex
assistance. The submitted contribution consists of the Lean proof of the
sharp special case, its finite-family/original-definition bridge, and
reproducible verification evidence. Prior mathematical results and reused
definitions retain their attribution and license.

Please assess statement fidelity, verification, overlap, and whether this
scoped formalization qualifies as a community contribution under the
[published rules](https://www.hejustinsun.com/prize/rules). In particular,
no improvement to the known mathematical special case is claimed; the
committee may judge that it does not constitute award-eligible progress.
No reward tier, amount, priority, organizer verification, or payment
entitlement is asserted. The full problem's solution and eligibility flags
are not changed. Passing repository checks concerns repository consistency,
not mathematical or award adjudication.
