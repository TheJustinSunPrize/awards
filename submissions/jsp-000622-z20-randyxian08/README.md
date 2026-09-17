# JSP-000622: closed Lean formalization of z(20) = 6

**Status: the closed twenty-vertex theorem has compiled and passed exact transitive axiom auditing. Independent review, archival and organizer assessment remain pending.**

This updates the planning-only document originally opened in PR #41; that history is preserved. This directory is an evidence index, not a vendored copy of the complete proof package. The proof source, generators, fixed dependencies, and actual verification receipts are linked below. No first-formalization priority, prize eligibility, recipient allocation, award decision, or payment entitlement is asserted.

## Exact scope and statement

This contribution addresses the **twenty-vertex sub-question associated with [Erdős Problem 758](https://www.erdosproblems.com/758) / [JSP-000622](../../problems/catalog-0601-0700.md#JSP-000622)**. It does not determine the extremal parameter for every number of vertices.

The cochromatic number is the least number of vertex classes, each inducing either a clique or an independent set. Empty colour fibres in the formal representation mean that `CochromaticColorable G k` uses at most k nonempty classes.

The compiled closed declarations include:

```lean
JSP000622.z_twenty_eq_six : Erdos758.z 20 = 6

JSP000622.JSP_000622 :
  (∀ G : SimpleGraph (Fin 20), Erdos758.CochromaticColorable G 6) ∧
  (∃ G : SimpleGraph (Fin 20), ¬Erdos758.CochromaticColorable G 5)
```

The main theorem has no certificate, classification, graph-packing, or other unproved mathematical hypotheses. Further compiled statements identify the literal maximum of individual cochromatic numbers, show attainment, and transport the upper bound to every finite vertex type of cardinality twenty.

## Immutable proof source and successful checks

Proof repository: `randyxian08/jsp000958-lean`; the development is isolated on `work/jsp000622-z20-verification` and does not alter that repository's unrelated main-branch proof.

- [Main theorem at the checked commit](https://github.com/randyxian08/jsp000958-lean/blob/3773abab463d0c58d92bdf200d5397a826385988/Z20/JSP000622/Main.lean).
- [Instantiation of every finite evidence obligation](https://github.com/randyxian08/jsp000958-lean/blob/3773abab463d0c58d92bdf200d5397a826385988/Z20/JSP000622/FiniteEvidence.lean).
- [All analytic source, generators and verification drivers at the checked commit](https://github.com/randyxian08/jsp000958-lean/tree/3773abab463d0c58d92bdf200d5397a826385988/Z20).
- [Statement correspondence and source attribution](https://github.com/randyxian08/jsp000958-lean/blob/3773abab463d0c58d92bdf200d5397a826385988/Z20/STATEMENT_AND_PROVENANCE.md).
- [Successful closed-theorem build and audit, run 35174067645](https://github.com/randyxian08/jsp000958-lean/actions/runs/35174067645).
- [Exact generated sources, compiler output and axiom receipt](https://github.com/randyxian08/jsp000958-lean/actions/runs/35174067645/artifacts/10477952116).

The source snapshot was `3773abab463d0c58d92bdf200d5397a826385988`. The successful run recorded exit code 0 for all of:

```text
lake build JSP000622.R34Nine
lake build JSP000622.FiniteEvidence
lake build JSP000622.Main
lake env lean ClosedAudit.lean
```

All eight explicitly required declarations were present and had the exact transitive axiom set `[propext, Classical.choice, Quot.sound]`:

```text
JSP000622.R34Seven.complete
JSP000622.R34Eight.complete
JSP000622.FiniteEvidence.complete_sixteen
JSP000622.FiniteEvidence.packing_twenty
JSP000622.z_twenty_eq_six
JSP000622.maximum_cochromatic_twenty_eq_six
JSP000622.colorable_six_of_card_twenty
JSP000622.JSP_000622
```

Thus the final checked declarations do not depend on `sorryAx`, project-specific axioms, or native-reduction/compiler-trust axioms. This conclusion comes from actual Lean output, not a source keyword search.

Closed-theorem artifact metadata:

```text
name: z20-closed-theorem-35174067645
artifact ID: 10477952116
bytes: 155402683
SHA-256: 87a311890369469fb8b7a8fdf59214e64801fb202caa116d17b4d9c6c2d3aada
```

The artifact has finite GitHub Actions retention. The [complete source release](https://github.com/randyxian08/jsp000958-lean/releases/tag/jsp000622-z20-verified-20260917) additionally preserves the generated source and closed-stage evidence outside the expiring artifact. Independent permanent archival remains outstanding.

Release assets:

- [Complete source ZIP](https://github.com/randyxian08/jsp000958-lean/releases/download/jsp000622-z20-verified-20260917/JSP000622_z20_complete_source_reissued.zip): 1,650,970 bytes; SHA-256 `6dcfd78f08d0440c2b032bafca10df2741224d8b3a13261725e8c38b19300b58`.
- [Source correspondence manifest](https://github.com/randyxian08/jsp000958-lean/releases/download/jsp000622-z20-verified-20260917/source-correspondence.json): all 971 packaged files under `JSP000622/` match the generated CI project byte for byte. The eight included closed-stage evidence files also match the downloaded artifact.
- [Asset hashes](https://github.com/randyxian08/jsp000958-lean/releases/download/jsp000622-z20-verified-20260917/SHA256SUMS).

The packaged `bash verify.sh` entry builds the supplied finite proof source without requiring SAT regeneration. Its wrapper is a distribution addition; the successful CI record verifies the matching proof modules, not a fresh extraction of this ZIP. A fresh kernel replay is optional via `bash verify.sh --fresh` and is not claimed by the closed-stage receipt.

## Proof organization and finite coverage

The lower bound follows from the previously formalized `z(16) = 6` and induced-subgraph monotonicity, and is also exported as existence of a twenty-vertex graph not colourable with five homogeneous classes.

For the upper bound, two disjoint homogeneous four-sets, together with the existing twelve-vertex upper bound, give six classes. A first four-set comes from the Ramsey bound. After complementation, its complement either has a second four-set immediately or is a sixteen-vertex (4,4)-Ramsey graph.

The universal sixteen-vertex classification is proved using the degree-seven-or-eight restriction, complete seven- and eight-vertex (3,4)-catalogs, all 27 normalized crossing-edge cases, and explicitly checked isomorphisms. Small-catalog completeness is an induction over every new-vertex adjacency pattern, not an assumption about the graph atlas or canonical-labelling software. All 3,299 extension patterns are covered. The 49 catalog-extension modules and 27 sixteen-vertex modules passed compilation and axiom audits in the six successful classification shards of run 35172668078.

Both fixed-core twenty-vertex graph-packing theorems passed compilation and exact axiom auditing in run 35173223882. Every retained CNF clause has explicit graph-semantic witnesses. The generic soundness theorem converts a reconstructed LRAT proof into the required graph packing. Formula equality, cardinality, disjointness, complement restoration and vertex relabelling are checked in Lean.

The aggregate catalog, universal classification, twenty-vertex packing and final extremal statement then passed together in run 35174067645. This is more than successful checking of isolated SAT instances.

## Pins, reproduction and trust boundary

```text
Lean: leanprover/lean4:v4.33.0
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d
Small-order proof: plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e
Original core certificates: ipitchford/z20-cochromatic@3c7e520fdc0615f5c700761c2b1e5108dcc836e7
```

A cache-independent reproduction entry point is included at the checked commit:

```bash
git clone https://github.com/randyxian08/jsp000958-lean.git
cd jsp000958-lean
git checkout 3773abab463d0c58d92bdf200d5397a826385988
bash Z20/reproduce_complete.sh
```

The script reconstructs finite data, compiles the complete theorem, runs the exact axiom audit, and requests a fresh kernel replay. The recorded CI checks used dependency caches; a cold, offline rebuild of the compiler and all dependencies is not claimed. The closed-theorem receipt explicitly excludes fresh replay from that stage. The earlier workflow 35172668078 passed the six classification shards but failed the two core shards; workflow 35173223882 passed both repaired core shards but its join/replay job failed. Neither earlier workflow is presented as wholly successful, and neither establishes a successful fresh replay. The later dedicated closed-stage run 35174067645 succeeded. These recorded compilation and axiom checks must not be described as a successful fresh replay or an independent implementation of the kernel.

The Python and C++ generators, NetworkX isomorphism search, SAT solver and file hashes are not mathematical axioms. Lean reconstructs/checks the resulting proof terms and all graph-semantic side conditions. No external solver's answer is accepted as an unexplained proof premise.

## Existing contributions and concurrent work

The mathematical two-core reduction and original SAT certificates follow the published [ipitchford/z20-cochromatic candidate](https://github.com/ipitchford/z20-cochromatic/tree/3c7e520fdc0615f5c700761c2b1e5108dcc836e7), with its original contributor and AI-system provenance retained. That project's CC0 dedication does not relicense unrelated third-party material.

The [existing small-order Lean development](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos758) was actually rebuilt and audited for this work. Its mathematical and formal contributors retain their published credit. No new mathematical discovery of `z(12) = 4`, the small-order table, or the pre-existing two-core strategy is asserted.

The new contribution presented for assessment is this proof-producing classification route, its coverage and graph-semantic interfaces, the complete normalization and aggregation, and reproducible closed-theorem verification. OpenAI ChatGPT assisted this continuation; the earlier planning document recorded its own assistance history. The submitting public account is `randyxian08`, which has a direct interest in any eligibility review. No recipient identity, allocation, private contact information or payment details are published here.

[PR #332](https://github.com/TheJustinSunPrize/awards/pull/332) reports another formalization for the same twenty-vertex target. This submission does not assert first-formalization priority, displace that contribution, or claim that the earlier planning draft reserved the problem. The other submission's correctness and priority are matters for its own evidence and the organizers' review.

## Requested review and remaining administrative steps

Please assess statement correspondence, the complete proof artifacts, contribution attribution, reproducibility, the applicable safe toolchain version, permanent archival and the proper intake location for this twenty-vertex extension. Independent substantive verification, recipient confirmation and an organizer decision remain pending.

No catalog flags, candidate records, award records, recipient records, decisions or generated repository data are changed by this evidence update. A successful proof build is not an award announcement or a payment authorization.

## Formalizer nomination and chronology

Please consider this completed formalization for formalizer eligibility and recipient review, with provisional ID `RECIPIENT-JSP-000622-A`. The submitting account authorizes public attribution to `randyxian08`; organizer confirmation remains pending. This is a self-submission with a direct interest in any award outcome. Existing mathematical, source and certificate attribution above remains applicable.

PR #41 was opened on 2026-09-16 at 11:48:26 UTC as a planning-only draft. Successful closed-theorem verification was recorded on 2026-09-17 at 02:23:59 UTC, and the evidence index was added in commit `782ca4291b62818d113181f862d081c2d8189b49` at 02:31:13 UTC. This update retains that chronology and requests substantive review of the now-complete submission. The initial planning date is not represented as the date a complete proof was submitted. Related PR #332 opened on 2026-09-17 at 00:33:38 UTC; attribution and any priority assessment are left to the organizers.
