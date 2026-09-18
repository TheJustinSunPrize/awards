# Draft: JSP-000733 — refined upper bound for primitive subset sums

Prepared submission text. Publication status and immutable evidence references belong to the accompanying pull request.

This formalizes the known upper bound for the actual maximum cardinality
f(n) of a subset of {1,...,n} whose numerical nonempty subset sums form a
primitive set. It proves, for every n >= 32,

    f(n) <= log_2(n) + (1/2) log_2(log_2(n)) + 3,

and the corresponding eventual statement with an existential constant.
The final theorem has no extra distinct-subset-sums, moment, or maximum
attainment assumptions. A separate declaration unfolds the maximum into
the original numerical-image condition; attainment is proved.

The primitive-to-injective bridge is adapted with attribution from the
Apache-2.0 additions in PR #31 at 83f20bbe58d116a9a290c86821fa4ee1a29dd3eb.
That PR covers the leading asymptotic and explicitly excludes this refined
error term. Generic second-moment bounds already have stronger formalized
source elsewhere; this package makes no novelty claim for those lemmas
and contains no copied lean-genius source.

Lean 4.33.1 and all nine dependencies are pinned. The package includes
actual build, fresh project compilation, statement/axiom audit, negative
test, and same-kernel fresh replay records. See logs/results.json for the
final run identity, result, and hashes of the exact checked source bytes.
The allowed axiom set is propext, Classical.choice, Quot.sound. Official
dependency caches were used; no second kernel implementation was run.
Evidence files are labeled path-redacted copies, with the originals kept
locally and both hashes recorded.

The complete source and redacted evidence are included in the proposed awards
submission directory. Official repository validation, links, build, data check,
history checks, and all 22 tests passed on the complete local change. These
structural checks do not verify the mathematics. Default whole-diff whitespace
checks reported retained evidence line endings; source and documentation checks
with CRLF recognized passed. Original failed diagnostics remain disclosed.

Permanent archival, any operator-designated independent verification, eligibility,
and an award decision remain pending. No recipient nomination, allocation,
global-priority claim, or payment entitlement is asserted. Source and release
references are supplied in the actual pull request; no pending check is marked
as an official success.
