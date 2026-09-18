# Scoped formalization review request: JSP-000389

Please assess the attached Lean formalization of classical factorial-residue
bounds and necessary conditions for socialist primes.

The [catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000389)
asks about the size of the factorial-residue set. Its current status is Progress,
and its eligibility flag is No. This submission does not override those flags.
The package proves the four explicitly scoped components in [README.md](README.md).
It does not prove the asymptotic formula, exclude all socialist primes, or assert
the stronger published analytic lower bounds.

The [reference formal statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/478.lean)
uses the same natural-remainder cardinality as `residueCount`. It is a statement
reference only, not an imported proof dependency.

The proof is [pinned at commit 3ab06d1f57b76a0573da1003b126f1df4a96abda](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/3ab06d1f57b76a0573da1003b126f1df4a96abda/projects/jsp-000389).
The local proof and reproduction files are byte-identical to that source.
The original research authors and Mathlib receive the credits described in the
README. The submitted work is the independently written formalization, prepared
with OpenAI ChatGPT assistance. No new mathematical discovery, first-formalization
priority or independent human verification is claimed.

Proposed recipient: `RECIPIENT-JSP-000389-KZ-A`, confirmation pending.
This is a self-submission with an interest in the assessment outcome. No private
identity, contact or payment data are supplied.

Please review statement fidelity, formalization scope, provenance, overlap,
reproduction and eligibility of these classical partial components. Redirect the
package if the repository requires a different intake location. Existing
catalog, candidate, award, recipient and schema records are unchanged.
Repository CI alone is structural validation and does not determine an award.
No organizer approval, allocation or payment entitlement is asserted.
