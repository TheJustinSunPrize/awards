# JSP-000692 / Erdős 836: question 2

This submission supplies a Lean formalization of the linear intersection bound
for **question 2 only** of [JSP-000692](../../problems/catalog-0601-0700.md#JSP-000692).
It is submitted for proof, statement, attribution, priority, and prize-eligibility
review. The separate vertex-count question is not formalized here.

## Verified scope

For every finite r-uniform intersecting hypergraph with r >= 2 and no proper
two-coloring, there exist **distinct** edges E and F satisfying

```text
r <= 2 * |E ∩ F| + 1.
```

Intersectingness then gives `r / 3 <= |E ∩ F|` for all r >= 2.
`JSP692.jsp000692_question_two` states the original three-chromatic version
with all finite vertex counts and all ranks quantified, using constant 1/3.
See [the mathematical argument](MATHEMATICS.md) and
[the definition correspondence](STATEMENT.md).

## Reproduction and actual evidence

Lean and Mathlib are pinned to v4.19.0; `lake-manifest.json` fixes the Mathlib
commit to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and pins its dependencies.
Install the pinned toolchain, then run from this directory:

```sh
lake exe cache get
bash verify.sh
```

The local macOS environment encountered a dyld compatibility failure when
starting the old native cache executable. Running the same cache program
through Lean worked:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

The proof sources themselves required no modification. Both `lake build` and
`lake env lean JSP000692.lean` passed. `Audit.lean` prints all nine project
theorems' dependencies; they are only `propext`, `Classical.choice`, `Quot.sound`.
The sole compiler warning concerns an unused `Fintype` section variable in
`edge_disjoint_of_independent`; it is not an admitted proof.

Original local evidence: [receipt](verification/status.json),
[build output](verification/review-original-build.log),
[axiom output](verification/review-axioms.log),
[standalone output](verification/review-standalone.log).
The receipt's `external_submission_performed: false` records the review stage
at its timestamp, before publication of this PR.

The module and standalone versions intentionally define the same declarations;
do not import them together. Comments saying NOT COMPILED record the original
authoring status; the dated evidence above supersedes that status.

## Attribution, related work, and requested assessment

The submitting account is randyxian08. Preparation and review used OpenAI Codex
assistance. The proposed formalization recipient placeholder is
`RECIPIENT-JSP-000692-A`, pending confirmation. The submitter has an interest
in assessment of this formalization contribution.

[Liam Price's 27 April 2026 forum post](https://www.erdosproblems.com/forum/thread/836#post-5941)
already reports a GPT-5.5 Pro solution of the second question. The linked
manuscript was not available for a full comparison during this review.
No mathematical discovery or first-formalization priority is claimed.
Prior contributors must be considered in the attribution review.

[Issue #50](https://github.com/TheJustinSunPrize/awards/issues/50) concerns the
separate first question, Alon's vertex-count counterexample. This package
addresses the second question and does not claim that work.

Please assess the proof, original-problem correspondence, contribution and
priority relative to existing work, and eligibility of this question-2
formalization. This directory is a proposed intake path; please redirect if
another location is required. Local success does not establish organizer
verification or entitlement to payment. No independent second checker was run.
No catalog flag, candidate record, recipient profile, or award record is changed.
