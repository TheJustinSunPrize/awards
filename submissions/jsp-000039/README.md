# JSP-000039: public evidence submission

This is a public evidence submission for JSP-000039.
It does not announce an award.
The submitter is GitHub user @linmanshan050813-dotcom.
Recipient confirmation is pending.
No private contact, payment, or identity documents are included.
Contribution type: proof/research material for review.

Related official record:
[JSP-000039: DGG cost-preserving conjecture](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000039).

## Contribution and attribution

This package presents a price-parameter analysis of a fixed nine-edge,
single-source network and a Lean proof for its explicitly enumerated routing
model. For nonnegative rational prices, it determines the exact minimum
feasible routing cost and the strict gap conditions. At prices
`(a,b,c) = (2,13/4,2)`, the reference fractional cost is `119/2`,
the minimum routing cost is `60`, and the gap is `1/2`.

The official catalog already credits Dmitry Rybin for discovery and Jason
Hickey for the referenced formalization. Those credits are preserved. This
submission asserts neither discovery priority nor independent verification of
the original result. The derivation, Lean preparation and documentation were
prepared with AI assistance (Codex). The submitter requests review of this
research package; attribution, novelty, conflicts and prize eligibility remain
for review. No reviewer independence or recipient attestation is asserted.

## Files

| File | Purpose |
| --- | --- |
| [proof.md](proof.md) | English derivation, theorem mapping and exact scope limits |
| [Submission.lean](lean/DGGCounterexample/Submission.lean) | Network data, route model, conservation and feasibility enumeration |
| [CostPerturbation.lean](lean/DGGCounterexample/CostPerturbation.lean) | Minimum cost, budget equivalence, price conditions and concrete gap |
| [Audit.lean](lean/Audit.lean) | Transitive axiom queries for the principal declarations |
| [REPRODUCE.ps1](lean/REPRODUCE.ps1) | Fail-fast local build, source scan and axiom report |
| [VALIDATION.md](VALIDATION.md) | Executed checks and remaining verification work |
| [SHA256SUMS](SHA256SUMS) | SHA-256 of every submission file except this checksum manifest itself |
| [ARTIFACTS.tsv](ARTIFACTS.tsv) | SHA-256 and byte count of evidence/source artifacts |

## Reproduction

Install the Lean toolchain manager `elan`, with its `lean` and `lake` commands
on PATH. The toolchain is `leanprover/lean4:v4.34.0`; the committed Lake
manifest pins mathlib at `5ed2965256430c3649e86755f9576b54eca72435` and
pins its transitive dependencies. From this directory:

```powershell
cd lean
./REPRODUCE.ps1
```

Equivalent build and audit commands, from `lean/`:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Use the committed manifest. Do not run `lake update` as part of reproducing
this revision. Dependency downloads require network access; toolchains,
dependency caches and compiled objects are excluded from the submission.
The script writes fresh output to ignored `lean/reproduction/`.

## Verification scope

The checked Lean theorems quantify over `Route := Terminal -> Choice`,
with two explicitly defined choices per terminal. The original proof sources
are unchanged from the locally prepared package.

**Known formalization gap:** `DGG.path_complete` proves that a listed choice
belongs to the path list. It does not establish that every directed graph
path is on that list. The bridge from arbitrary graph paths to `Route`, and
the bridge from a general edge-sum cost to the defined cost formulas, are
explained in [proof.md](proof.md) but are not formalized in this version.
No theorem in this package states the full graph-level DGG conjecture or its
negation. Local compilation establishes the stated finite-model theorems.

## Intake and pending items

At official main commit `f4e7173d89dfe91022a185427d63452c8ffbf6ae`, the problem
index records this entry as Solved, Lean proof Yes, Eligible to claim Yes,
and Unclaimed. These markers are not an award or a formal candidate record.

This `submissions/` directory is proposed as evidence for maintainer intake.
It changes no candidate YAML, recipient profile, verification attestation,
published decision, award tier or payment instruction. Acceptance of this
layout remains a maintainer decision. The [record guide](../../docs/records.md)
and [contribution rules](../../CONTRIBUTING.md) govern subsequent official
records. An initial recommendation is distinct from a formal candidate;
unconfirmed recipient records must use the official placeholder mechanism.
The public GitHub username above identifies the submitter only.

Pending: maintainer intake, attribution/conflict review, recipient confirmation,
independent reproduction, graph-level statement comparison and review
signatures, and permanent external archival. No external archive ID, independent
checker record or signed verification statement exists for this package yet.
Local SHA-256 values and byte counts do not substitute for such an archive.
