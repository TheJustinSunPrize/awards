# Updated review request: full bound and matching stars

This supplement extends the same JSP-000438 / Erdos 547 submission in PR #408.
It makes no separate reward application.

The package now proves both:

- For every n >= 2 and every n-vertex tree T, R(T,T) <= 2n-2.
- For every natural k, the star on 2k+2 vertices has Ramsey number exactly
  4k+2. Thus every even tree order attains the upper bound.

The new code is StarSharpness.lean. It supplies an explicit cyclic coloring
on 4k+1 vertices, both degree bounds, absence of either monochromatic star,
a restriction argument for smaller hosts, and the exact Ramsey equality.
The endpoint tree_ramsey_bound_is_sharp combines the general upper bound
with all the matching examples. The k=0 boundary case is included.

The general upper bound continues to depend on the existing tadamcz/erdos548
proof at 82ffb751f3d37768927df9239ed08439bbe0dd09, with all original credit,
license, original source and port history retained. These star examples and
Ramsey implications are classical mathematics. The contribution is their
formal integration and verification; no new mathematics, upstream proof
ownership or first-formalization priority is claimed. OpenAI ChatGPT assisted.

Fixed supplement proof:
https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438

Remote verification:
https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177382098

See SHARPNESS.md for the argument and VERIFICATION.md for the actual check
results and artifact limits. INITIAL_SUBMISSION.md, INITIAL_VERIFICATION.md,
INITIAL_PROOF_SHA256SUMS and INITIAL_PROOF_WORKFLOW.yml preserve the original
review request and verification snapshot. Existing historical logs are retained.

The independently added [finite-color supplement](supplements/multicolor/README.md)
is preserved with its own pinned proof and verification receipt. The sharp-star
verification above does not replace that separate evidence.

The proposed recipient remains RECIPIENT-JSP-000438-KZ-A, confirmation pending.
This is a self-submission by ketianzhang1-lang. Please assess the full statement,
sharpness supplement, attribution, overlap, eligibility and intake placement.
No catalog, candidate, recipient confirmation, award or payment record is
changed. Machine verification does not itself constitute organizer approval
or entitlement to an award.
