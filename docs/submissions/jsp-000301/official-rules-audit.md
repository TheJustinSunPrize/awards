# Official website rules: correction and application to this submission

Accessed **2026-09-17**. This supersedes the packet's earlier repository-only
assessment of publicly available prize terms. It does not alter the proof,
claim a tier, establish priority, or constitute an organizer decision.

## Sources and exact quotations

The user-supplied [About page](https://hejustinsun.com/zh/prize/about) directly
links the [Selection Rules](https://hejustinsun.com/zh/prize/rules),
[Claim Guidelines](https://hejustinsun.com/zh/prize/claim),
[FAQ](https://hejustinsun.com/zh/prize/faq), and
[Terms](https://hejustinsun.com/zh/prize/terms). All five were successfully
retrieved with TLS certificate verification. Their returned text is English
despite the `/zh/` URL. Quotations below preserve that English wording.
The Rules identify **v1.0**, published and effective **September 16, 2026**;
the Terms carry the same effective date. Response hashes and byte counts
are recorded in [source metadata](evidence/official-website-sources.json).
The hashes identify what was read; no permanent web archive is claimed.

| Exact quotation | Official location | Consequence |
| --- | --- | --- |
| “Open globally to researchers, independent contributors, human-AI teams, and AI systems.” | About, Quick Facts | AI assistance is not itself a disqualification. Legal applicant/payee conditions still apply. |
| “Disbursement is pegged at $1,000,000 USD per verified closure.” | Rules §3.1, Pinnacle | This is a gross allocation for an officially designated Pinnacle closure, not the overall program pool or a promised amount for JSP-000301. |
| “Allocations across Tiers II through V are adjudicated by the Academic Committee and published upon review.” | Rules §3.1, Operational Note | The four other tiers do not have fixed amounts on these pages. |
| “Bounty eligibility extends retroactively to qualifying achievements completed on or after January 1, 2026.” | Rules §2.5 | The date is a qualification condition; a recent compilation does not make an old mathematical discovery new. |
| “Lean formal verifier: the individual or team that completes the Lean formalization and submits the verified PR will receive 30% of award allocation.” | Rules §5 | This is a role allocation conditional on an actual award, not an entitlement for every formalization submission. |
| “Where multiple independent contributors achieve the solution within the same evaluation window, joint awards may be conferred.” | Rules §5 | Joint treatment cannot be self-certified. The organizer must determine the applicable window and qualifying contributors. |
| “Once verified, the PR is merged to establish eligibility, lock the priority timestamp, and advance the submission to evaluation.” | Rules §6, PR Finalization | Local compilation and opening a draft PR do not complete the official verification/evaluation path. |
| “Priority for Lean formal verifiers is determined solely by the timestamp of first public visibility, regardless of the platform.” | FAQ Q8 | Prior public formalizations matter across platforms. |
| “It is not based on the time of submission or merging into the Prize system—the Prize's internal processing speed does not alter established external chronologies.” | FAQ Q8 | Do not treat this PR's eventual merge as a way to overtake prior public work. |
| “Account control serves solely to establish the claimant's association with the relevant account, and does not independently constitute proof of actual contribution to or ownership of the awarded contribution.” | Claim Guidelines §II.1 | The publishing account is not sufficient recipient/ownership confirmation. |
| “Prize claims and related processing are handled exclusively through the official contact email of the Justin Sun Prize.” | Claim Guidelines §VII | The issue is evaluation intake and clarification, not the later payment-claim channel. |

## What the official rules now establish

There are **five** tiers: Pinnacle, Breakthrough, Landmark, Advance and
Contribution. Only Pinnacle has a fixed published gross allocation of
USD 1,000,000 per qualifying verified closure. Rules §3.1 reserves it for
designated foundational bottlenecks. Tiers II–V are committee-determined;
we do not assign JSP-000301 a tier or infer an amount from its complete
formal disproof. Rules §4.2 distinguishes full resolution from substantial
resolution, partial progress and no progress; completion alone does not
determine priority, eligibility or payment.

Rules §5 assigns **70% to the first mathematical solver** and **30% to the
Lean formalizer**, with 100% only when both roles belong to the same entity.
This packet does not claim the solver role for the historical counterexample.
The 30% is a share of an awarded problem allocation, not 30% of USD 1,000,000
for this submission. Whether it can receive any formalization allocation
depends on organizer verification, priority, possible joint treatment and
the actual award decision.

Human researchers, human-AI teams and autonomous AI systems are admitted by
Rules §5 and §8.1; prior academic publication is not a prerequisite. The
same section requires team representatives and lawful payees, and a natural
person, legal entity or written authorized representative for autonomous-AI
claims. Nothing here invents a legal identity, authorization, signature,
team allocation, or ownership confirmation.

Rules §4.1 and §6 establish the ordinary route: a Lean statement, proof and
evidence PR to the designated repository, designated isolated verification
including axiom and independent-checker review, verified PR finalization,
and three-criteria evaluation. Academic Committee recommendations/signatures
and Organizing Committee authorization are described in §§2.3, 4 and 6.
The registration alternative is for already-public formalizations broadly
recognized as peer-verified; a public fork plus self-run `leanchecker` does
not establish that alternative's prerequisites (Rules §4.1; FAQ Q5, Q9).

The [Claim Guidelines](https://hejustinsun.com/zh/prize/claim), introduction
and §I, apply after official publication of eligible-claimant status or
confirmed awards. They require the claimant to check the published identity,
role and contribution, initiate contact by official email, and undergo
identity, contribution-ownership and authorization checks. Formal award
confirmation precedes payment-detail submission, compliance review and
disbursement. Being listed as an eligible claimant is itself not formal
award confirmation. A GitHub issue is therefore not a substitute for this
later proactive claim process.

The public contact link on About resolves to
**thejustinsunprize@hejustinsun.com** (decoded from the page's public
Cloudflare email obfuscation). No claim email has been sent for this packet:
there is no verified announcement naming a claimant for it and no confirmed
legal claimant information. Sensitive documents and payout details belong
only in the official private process, never in this repository or issue.

Rules §§2.6 and 3.3 specify cryptocurrency and mandatory KYC; payout options
are **TRC-20 USDT or ERC-20 USDC**, one option per payout. Claim Guidelines
§III describes a 1 USD to 1 USDT/USDC basis in principle, with any different
conversion communicated and confirmed before transfer. Sections V–VI cover
tax responsibility and deadlines set by announcements or official emails;
no specific deadline or net payout for this packet has been established.

## Priority risk and current eligibility conclusion

Multiple prior JSP-000301 formalization PRs and intake issues were disclosed
in the [packet README](README.md). We have not established first public
formalization priority, independently validated every earlier proof, or
obtained an organizer determination of the evaluation window. Code style,
an additional local kernel check, and a new PR do not override valid earlier
public results under FAQ Q8.

**This packet is not currently eligible for a payment claim:** it has a
draft PR and self-check evidence, not completed designated verification,
verified PR finalization, official eligible-claimant publication or award
confirmation. This is a failure to meet the current claim-stage prerequisites,
not a conclusive finding that the organizer can never recognize its
contribution. If an earlier valid formalization has priority and no applicable
joint award is available, this packet has no established right to the
formalizer allocation. We do not seek to displace earlier work or claim the
historical solver's 70%.

A supplementary rewrite cannot establish first-formalization priority or
an entitlement to 30%. If same-window joint treatment is unavailable, the
organizer may be asked whether this work is eligible for consideration under
Tier V (Contribution). We do not assert that this tier applies, that it
bypasses the priority rules, or that any award is due.

The compliant next step is to keep the existing PR/issue as supplementary
evidence, request consolidation if appropriate, and ask the designated
authority to determine priority and any joint eligibility. If ineligible,
retain it as an unawarded contribution; any attempt at a different still-eligible
problem would require a fresh scope and prior-art check, not relabeling this
known example as a new solution. No duplicate issue or premature payment
claim is needed.

## Text discrepancies needing organizer interpretation

The FAQ and Claim Guidelines defer to the Selection Rules; Terms §2 states
that the Rules govern evaluation and allocation, and Terms §8 gives the
English text precedence over conflicting translations. We do not invent a
resolution of the following discrepancies:

- Rules §6 refers to locking priority on PR finalization, while FAQ Q8
  explicitly says first public visibility determines chronology. We preserve
  the external public chronology and ask the organizer to confirm its
  administrative treatment; merge timing is not asserted as substantive
  priority.
- FAQ Q15 says: “The Prize Operator will cover all network transaction fees
  incurred during prize disbursements via the TRON or Ethereum networks.”
  Terms §4(2) says: “Network gas fees and exchange/processing fees generated
  from on-chain transfers shall be borne by the recipient in accordance with
  the specific payment channel rules.” Actual fee treatment therefore needs
  written confirmation before any payout; no net amount is promised.
- The website has five tiers, whereas the current repository
  [award schema](../../../data/schema/award.schema.json) permits levels 1–4.
  This packet does not modify the schema or assign a level. An authorized
  mapping or schema decision is required if a live award record is prepared.

## Correction to the earlier application

Earlier versions inspected only repository materials and described the
allocation rules, AI eligibility, formal application path and payment
procedure as unknown. Those broad gaps are now resolved by the official
website and are superseded by this audit. What remains unknown is **this
packet's** acceptance, priority/joint eligibility, designated review outcome,
awarded tier and amount, confirmed recipient, and eventual payment decision.
The generic role percentages and claim procedure are no longer presented
as unpublished. PR #440 and issue #441 are updated in place; no new intake
is created. The Lean source and successful proof evidence are unchanged.
