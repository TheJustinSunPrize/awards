# JSP-000301: supplementary formalization evidence for review

This documentation packet supplies an AI-assisted Lean formalization of the
**already-known** counterexample 12167, 12168. It is not a live candidate
record, an independently signed verification record, a claim of first
formalization, or an award decision. Recipient attribution remains unconfirmed;
`RECIPIENT-JSP-000301-A` is a placeholder for this intake only, not an assertion
of identity with placeholders used in other submissions.

**VERIFIED locally:** Lean 4.34.0 compilation and same-toolchain `leanchecker`
replay both returned exit code 0. The two main theorems depend only on
`propext` and `Quot.sound`. Independent review remains pending.

## Exact result and reproduction

The [catalog](../../../problems/catalog-0301-0400.md#JSP-000301) asks whether
two consecutive powerful positive integers must include a square. Its
review notes explicitly exclude the separate counting question.
The [mathematical explanation](../../jsp-000301-powerful-counterexample.md)
and [Lean source](proof/Counterexample.lean) answer this entire scoped question
negatively, rather than proving a weaker special case of a different claim.

`Powerful n` means `0 < n` and, for every natural prime p, `p ∣ n → p*p ∣ n`.
`prime_iff` proves that the source's prime definition is equivalent to the
usual unbounded divisor characterization. The main theorems produce the
counterexample and negate the original universal implication. Neither the
powerful nor the square predicate has a restricted domain of possible primes
or roots.

Use the [reproduction guide](proof/README.md) and pinned toolchain to compile
the actual source and replay its declarations. The source SHA-256 is
`8849a0a8c2295e852c3ef5203a2b112b70a7d019471971bc9b4c75efc97b265a`.
The [successful build log](evidence/lean-build.log),
[version and hash metadata](evidence/lean-build.json), and
[replay output](evidence/leanchecker.log) are actual outputs.
See the [evidence summary](verification/local-evidence.md) and
[unsigned statement comparison](verification/statement-draft.md).

The compiler and replay utility share the Lean kernel; they are not two
independent verifiers. Bundled library artifacts were used, networking was
not explicitly disabled by the runner, and no memory cap was imposed.
An initial enumeration approach timed out and was replaced by the successful
algebraic proof. Earlier failure logs are labeled separately; they are not
the final proof's axiom audit.

## Related submissions and attribution

Before publishing this packet, the submitting account's existing PRs and
issues were checked; none concerned this work. The upstream already contains
other submissions for the same mathematical counterexample, including
[PR #13](https://github.com/TheJustinSunPrize/awards/pull/13),
[PR #17](https://github.com/TheJustinSunPrize/awards/pull/17),
[PR #33](https://github.com/TheJustinSunPrize/awards/pull/33),
[PR #55](https://github.com/TheJustinSunPrize/awards/pull/55),
[PR #103](https://github.com/TheJustinSunPrize/awards/pull/103),
[PR #108](https://github.com/TheJustinSunPrize/awards/pull/108), and
[PR #187](https://github.com/TheJustinSunPrize/awards/pull/187).
Related intake discussions include
[issue #64](https://github.com/TheJustinSunPrize/awards/issues/64),
[issue #82](https://github.com/TheJustinSunPrize/awards/issues/82), and
[issue #146](https://github.com/TheJustinSunPrize/awards/issues/146).
This list is not a priority ranking or an exhaustive attribution audit.

The mathematical counterexample was already in the catalog. This session
produced its own exposition, arithmetic checking and local formalization;
no first-discovery, first-formalization, or entitlement is asserted. This is
a supplementary packet for organizer review. Organizers may consolidate
the intake with related submissions. Public account authorship of a commit
does not establish a confirmed recipient identity or signed academic credit.

## Rules audit and remaining requirements

| Question | Source-backed finding |
| --- | --- |
| Amount and payment entitlement | **Unknown, not zero.** The inspected [grading rules](../../grading.md) publish no amount or payment calculation for this result. An empty historical bounty field is not an amount. No payment promise is inferred. |
| Separate formalization contribution | [About](../../about.md) and [attribution](../../attribution.md) distinguish discovery and formalization. They do not guarantee an award for this particular additional proof or establish its novelty. |
| Screening versus an award | The catalog's solved/Lean eligibility convention is not a nomination, award, or right to payment. This contribution changes no catalog flag, claim status, candidate, or award. See [about](../../about.md). |
| Intake | The [recipient recommendation form](../../../.github/ISSUE_TEMPLATE/recommend-recipient.yml) and [contribution guide](../../../CONTRIBUTING.md) supply an evidence intake route, not automatic acceptance or payment. |
| Formal review | [Verification](../../verification.md) and [records](../../records.md) require source pinning, statement comparison, axiom auditing, reproduction and independent review. Local compilation alone is insufficient. |
| Signatures and checkers | [Statement schema](../../../data/schema/statement.schema.json) requires at least two signatories. [Validation](../../../scripts/manage.py) requires authorized profiles and reviews of non-library definitions, distinct checkers, safe-version assertions and isolation controls for confirmed evidence. These are not supplied or fabricated here. |
| Historical dates | The catalog's proposal and first-counterexample dates are unverified. The live award schema requires a proposal year; no date is invented to satisfy it. No live award YAML is proposed. |
| Recipient confirmation | Pending. The placeholder does not identify the operator as a mathematical discoverer, confirmed formalizer, or award recipient. Identity, consent and conflicts require actual confirmation. See [attribution](../../attribution.md). |
| Final decision | An authorized public award announcement and completed verification/recipient requirements remain necessary. Payments are outside the repository. See [records](../../records.md) and [platform notes](../../platform-setup.md). |

On 2026-09-17, the official GitHub API returned an empty releases list and
an `awards/` directory containing only `README.md`. An official about-page
snapshot is retained with its Git blob identifier in the
[source-check record](evidence/official-source-check.json). These endpoints
do not establish that no announcement exists in any other official channel.
Raw-content access failed certificate validation; the API fallback succeeded
without bypassing TLS checks. Other contributors' descriptions of award
terms are not treated as independently verified official terms.

Requested organizer decisions are acceptance or consolidation of this
supplementary intake, an authorized independent verification route, whether
this additional formalization qualifies for consideration, and the applicable
public terms, amount and payment conditions. No amount, acceptance, reviewer
signature, discovery priority or award is asserted by this packet.

## Publication and validation

The contribution PR and recipient intake issue link an immutable Git commit
for this source and its evidence. Git hosting is not represented as a
permanent scholarly archive. No candidate or award record is introduced.
No private identities, contact information, payment details or local machine
paths are included. Final build and replay logs were copied without content
redaction: they contain no local absolute paths. The reproduction guide's
temporary installation path was replaced with portable PATH instructions;
the proof source and its successful build log were not altered.

The [integrity manifest](evidence/packet-manifest.json) records byte counts and
SHA-256 hashes of this packet. Repository validation results are reported in
the PR; those structural checks do not certify the mathematics or award
eligibility.
