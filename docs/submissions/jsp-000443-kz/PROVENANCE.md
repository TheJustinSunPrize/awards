# Scope, attribution, and duplicate screening

This is a self-submission of a scoped, independently written Lean
formalization prepared with OpenAI ChatGPT assistance. The mathematical
upper bounds and finite projective-plane construction are known results;
new mathematical discovery, global first-formalization priority and sole
manual authorship are not claimed.

The precise contribution is the source in `JSP000443.lean`, its explicit
equivalences with Mathlib graph copies, its finite witness and reproduction
package. The original problem remains open in general. No catalog flag,
candidate record, award record, confirmed recipient profile or payout
record is created or altered by this submission.

Historical references are listed in `README.md`. The original question is
attributed in the Formal Conjectures statement to Burr, Erdős, Faudree,
Rousseau and Schelp. Classical C4/star bounds and projective-plane
constructions are associated with Parsons's work. Mathlib's authors retain
credit for the imported mathematical infrastructure. No third-party
solution module is imported or represented as the submitter's work.

On 2026-09-17, the official awards repository's issue/PR search for the
literal identifier `JSP-000443` returned no matches before this submission.
The catalog at `f4e7173d89dfe91022a185427d63452c8ffbf6ae` lists Lean proof
as No and the problem as Progress / Eligible No / Unavailable. That limited
screening does not establish that no related proof exists elsewhere, and
does not justify changing the catalog's whole-problem status.

Proposed formalization contributor placeholder:
`RECIPIENT-JSP-000443-KZ-A`, confirmation pending. This is contributor-run
verification, not independent human review or an organizer attestation.
No curator/verifier role, private agreement, award allocation or payment
entitlement is asserted. Attribution, overlap, scope, priority and any
applicable contribution eligibility remain for organizer assessment.


## Infinite-family extension

PolarityFamily.lean formalizes the classical finite-field polarity construction
uniformly, with an injective family of neighbors and an algebraic common-neighbor
uniqueness proof. Its all-power-of-two equality is a known consequence; the
Parsons reference in README.md retains mathematical credit. This extension is
OpenAI ChatGPT-assisted implementation work and makes no global first-priority
claim. It supplements existing PR #379 and is not a new reward request for each
parameter. See FAMILY_PROOF.md for the exact additional scope.


## Earlier same-problem submission

[PR #134](https://github.com/TheJustinSunPrize/awards/pull/134), at head
`bf3b21b1dde6fbc9e0b023914e9e780695cebe8d`, already formalizes Boza's
Theorem 6 and Corollary 8. Its published scope is
`a+b <= f(a) or f(a+b) <= a+2*b` for positive a,b, and
`f(f(n)+1) <= 2*f(n)-n+2` for positive n. Those are different named targets
from this finite-field exact family. This comparison is based on the PR's
explicit theorem statements, not an independent rebuild of its source.
The earlier submission is acknowledged and no general first-formalization
claim for JSP-000443 is made. Organizers should assess any overlap.
