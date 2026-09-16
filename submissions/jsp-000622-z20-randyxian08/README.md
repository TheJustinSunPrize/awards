# JSP-000622: z(20) = 6 formalization work in progress

**Status: planning draft. This directory contains no Lean proof yet.**
No new mathematical result, completed formalization, independent verification,
priority reservation, eligibility decision, or award is claimed.

## Scope

This work targets the 20-vertex extension associated with
[JSP-000622](../../problems/catalog-0601-0700.md#JSP-000622) and
[Erdős Problem 758](https://www.erdosproblems.com/758).
The cochromatic number of a graph is the least number of vertex classes such
that each class induces either a clique or an independent set. Let z(n) be
the maximum cochromatic number over all graphs on n vertices.

The proposed target is **z(20) = 6**. A complete formalization must prove both:

1. Every graph on 20 vertices admits such a partition into at most 6 classes.
2. Some graph on 20 vertices admits no such partition into at most 5 classes.

This is distinct from the already publicly implemented z(12) = 4 result.
The organizers have not confirmed whether this extension is accepted under
this catalog entry or whether this directory is their preferred intake path.

## Existing work and attribution

- [Candidate proof and certificates by the ipitchford/z20-cochromatic project](https://github.com/ipitchford/z20-cochromatic/tree/8dc4b8cd31f4323d6a032752f4cfd69c06d5ca90).
  The project describes its result as an unrefereed computer-assisted candidate,
  not a complete Lean formalization. Its mathematical and computational
  contributions remain credited to its published authors and contributors.
- [Existing z(12) = 4 Lean implementation](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos758.lean).
  Its source credits Bhavik Mehta for the informal result and Codex / GPT-5.6 Sol
  for formalization. It has been inspected but not reproduced in this draft.
- [Candidate formalization blueprint](https://github.com/ipitchford/z20-cochromatic/blob/8dc4b8cd31f4323d6a032752f4cfd69c06d5ca90/lean_blueprint.md).
  This is a plan, not proof evidence. In particular, classification completeness
  and the correspondence between graph properties and computational encodings
  must be proved rather than assumed.
- [Related catalog evidence update, PR #40](https://github.com/TheJustinSunPrize/awards/pull/40).
  Existing public sources must be checked independently of catalog screening flags.

The submitting account is randyxian08, with OpenAI Codex assistance.
The submitter is interested in evaluation of any future completed contribution.
No recipient identity or allocation is proposed at this planning stage.

## Planned work and completion criteria

- [ ] Fix a Lean toolchain and library revision; define the target precisely.
- [ ] Reproduce and audit any existing formal results proposed for reuse,
      preserving their licenses and attribution.
- [ ] Formalize the lower-bound witness and exclude all five-class partitions.
- [ ] Prove the upper-bound reduction, including all classification and
      exhaustive-coverage obligations used by that reduction.
- [ ] Import or reconstruct computational certificates through a checked
      proof-producing route and prove the encoding correspondence.
- [ ] Close the final theorem without unproved mathematical assumptions.
- [ ] Run clean compilation, axiom audits, source hashing, and reproducible checks.
- [ ] Request independent review and organizer assessment before converting
      the draft into a completed-proof submission.

No milestone above is represented as complete by opening this draft.
The computational classification is a feasibility risk; successful certificate
replay by itself would not prove the full graph-theoretic statement.

## Requested handling

Please treat this as a work-in-progress scope notice, not a submission ready
for proof acceptance or prize evaluation. Please advise if work-in-progress
PRs or this extension belong elsewhere. Opening this draft does not reserve
the problem or prevent other contributors from working on it.

No catalog status, candidate record, award record, or generated data is changed.
