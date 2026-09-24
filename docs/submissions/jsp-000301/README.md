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

## Official rules and remaining requirements

**Correction, 2026-09-17:** the earlier audit inspected repository materials
only. The official [About](https://hejustinsun.com/zh/prize/about),
[Selection Rules](https://hejustinsun.com/zh/prize/rules),
[Claim Guidelines](https://hejustinsun.com/zh/prize/claim),
[FAQ](https://hejustinsun.com/zh/prize/faq) and
[Terms](https://hejustinsun.com/zh/prize/terms) have now been read directly.
The [detailed official-source audit](official-rules-audit.md) records exact
quotations, sections, access date, source hashes and corrections to the
previous application. Rules v1.0 were published/effective September 16, 2026.

| Topic | Established public rule and application here |
| --- | --- |
| Tiers and amount | Five tiers. Pinnacle: USD 1,000,000 gross per designated verified closure; Breakthrough/Landmark/Advance/Contribution: committee-determined. This packet has no assigned tier or amount; the Pinnacle allocation is not a program-wide pool or this example's bounty (Rules §3). |
| Role allocation | Solver 70%, Lean formalizer 30%, both roles together 100% (Rules §5). This known counterexample supplies no new solver claim; no automatic formalizer share or dollar amount is asserted. |
| AI participation | Human-AI teams and AI systems are permitted, subject to verified contributions and lawful applicant/representative/payee requirements (Rules §5; FAQ Q4, Q16). Identity and ownership remain unconfirmed. |
| Priority | First public visibility across platforms governs formalizer priority; code elegance and internal processing speed do not displace valid earlier work (FAQ Q8). Prior submissions exist; first priority is not established. Joint treatment is conditional on the organizer's evaluation-window determination. |
| Evaluation route | Lean PR and evidence → designated isolated verification → verified PR finalization → evaluation (Rules §§4.1, 6). A publicly peer-verified registration route also exists; self-checking does not establish peer verification. |
| Payment claim route | After official eligible-claimant publication, initiate via the official email; verify identity, ownership and authorization; obtain formal confirmation; only then provide payment details (Claim Guidelines I–III, VII). Issue #441 is an evaluation intake, not a payment claim. |
| Payout | TRC-20 USDT or ERC-20 USDC, subject to KYC/compliance and official confirmation (Rules §§2.6, 3.3). Taxes and deadlines follow the claim guidance. Conflicting website fee clauses require written clarification. |
| Current eligibility | No designated independent review, verified merge, official eligible-claimant publication or award confirmation exists for this packet. It is **not currently eligible for a payment claim**; any formalizer/joint eligibility remains an organizer decision. |
| Records | No official status, recipient, candidate or award record is changed. Unknown historical dates remain unknown. Website five tiers versus repository levels 1–4 requires authorized interpretation, not an invented mapping. |

The repository API checks in [the earlier source record](evidence/official-source-check.json)
remain accurate for those endpoints, but are not an exhaustive survey of
public rules and do not override the newly checked website. Requested next
steps are organizer acceptance or consolidation, designated verification,
priority/joint-eligibility determination and clarification of case-specific
award terms. If this later contribution is ineligible, it should remain an
unawarded supplementary contribution, not be relabeled as a new discovery.
No private claim email, identity document, legal signature or payout detail
has been supplied. See the detailed audit for the official contact and prerequisites.

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
