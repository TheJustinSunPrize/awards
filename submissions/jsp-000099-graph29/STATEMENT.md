# Scope and attribution: JSP-000099 / Erdős 82

**LOCAL VERIFICATION PASSED — OFFICIAL REVIEW OUTSTANDING.** This document specifies the claim proved by the locally checked Lean package. Official designated verification, attribution review, eligibility assessment, and any award decision remain outstanding. No submission or official acceptance is asserted here.

The proposed contribution formalizes a **known finite lower bound**, not a solution of the original open asymptotic conjecture.

## Exact target

There exists an undirected simple graph on 29 vertices such that every induced subgraph on at least seven vertices is nonregular. Equivalently, this is a witness for the known lower bound `N_{≥7} ≥ 30`, where `N_{≥7}` is the least order for which every graph has a regular induced subgraph on seven or more vertices.

“Regular” means that all vertices have the same degree **within the selected induced subgraph**. The degree may be zero. The quantifier covers every subset size from 7 through 29, not merely size seven.

More explicitly, the target is a simple graph `G` whose vertex type is `Fin 29` such that, for every finite vertex set `T` and every natural number `d`,

```text
7 ≤ T.card  →  ¬ (G.induce (T : Set (Fin 29))).IsRegularOfDegree d.
```

The concrete theorem is named `Erdos82Finite.graph29_no_regular_induced`; the existential theorem is named `Erdos82Finite.exists_graph29`. The existential statement includes a decidable adjacency relation for the graph. This is computational data, not an additional mathematical assumption restricting the graph class. Because the ambient vertex type is finite, the finite-set quantifier covers every vertex subset.

The final Lean statement uses Mathlib's `SimpleGraph (Fin 29)`, `SimpleGraph.induce`, and `IsRegularOfDegree`. The bridge theorem `Erdos82Finite.regular_correspondence` identifies Mathlib's regularity predicate with the degree predicate used by the certificate checker. The checked degree is within `T`, not within the ambient graph.

The Lean target is the graph witness. No separately defined Ramsey minimum `N_{≥7}` is claimed as a declaration in this package. Its lower-bound interpretation follows from the usual definition: a 29-vertex counterexample rules out a universal guarantee at order 29, and its induced subgraphs rule out such a guarantee at smaller orders. No upper bound at order 30 is supplied.

## Mathematical sources

- Paul W. Dyson and Brendan D. McKay, [*Ramsey numbers for regular induced subgraphs*, arXiv:2604.08215v3](https://arxiv.org/html/2604.08215v3), Theorem 1.2 and Section 5.
- Authors' [data page](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html), section “Regular induced subgraphs.”
- Original [compressed graph6 data stream](https://users.cecs.anu.edu.au/~bdm/data/regsub_ge7.29some.g6.gz).
- The selected witness is the **first graph6 line**, with 29 vertices and 202 edges. SHA-256 of that line including its LF: `464ffb9db0b700c3ba7104fabbd76e2e338e7276a1c4b1184f67bc9c6692033b`.

The graph and lower bound are credited to Dyson and McKay. The formalization contribution consists of the certificate checker, its correctness proof, the formal graph correspondence, and kernel-checked witness certificates. No mathematical discovery credit is claimed for the graph or bound. Mathlib and Lean dependencies retain their upstream attribution and licenses. Attribution to the mathematical authors does not assert that they have endorsed this package or consented to designation as prize recipients.

The author data is represented locally by `supporting-computation/e82-witness.g6`, its metadata and adjacency masks, and the explicit neighbor sets in `Graph29.lean`. The included provenance and independent data check connect these encodings to the selected source line and its recorded hash. The archive is a sample, so neither this work nor the source data is represented as a complete enumeration of every 29-vertex graph with the required property.

## Certificate argument

For a proposed common degree d, a search state records vertices already selected S and possible vertices U. Every candidate T satisfies S ⊆ T ⊆ U. The checker accepts only by combining the following proved rules:

1. If |U| < 7, no candidate is large enough.
2. If a selected vertex already has more than d selected neighbors, or fewer than d possible neighbors, no completion is d-regular.
3. A vertex whose degree cannot be d can be excluded.
4. If a selected vertex has exactly d possible neighbors, all those neighbors are forced.
5. If it already has exactly d selected neighbors, its other neighbors are excluded.
6. For any vertex, include and exclude branches cover every candidate.

The invariant `S ⊆ T ⊆ U` is part of the generic soundness theorem. Each rule either proves that no candidate can satisfy the invariant and target, or preserves all possible candidates in the remaining child states. In particular, a branch whose state cannot contain a candidate does not create a false positive for the original state.

The mask representation is connected to finite sets by a separate proved decoding correspondence. Checkpoints store concrete selected and possible masks; acceptance requires exact equality with the state being checked. The proof may be divided into small certificates whose acceptance theorems are composed. This changes proof organization, not the candidate subsets or degree range.

The external generator merely proposes certificates. The Lean correctness theorem and the checked certificate proofs validate them. The preliminary C++ exhaustive search is supporting evidence, not an axiom or a premise of the theorem. The final combination covers degrees `0` through `28`; any regular induced subgraph in a simple graph on 29 vertices has degree below 29, so no higher degree is omitted.

## Relationship to JSP-000099 and award scope

The [official catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000099) asks how large a regular induced subgraph is guaranteed in an arbitrary graph of given size. The reviewed catalog lists the Dyson–McKay paper among its sources and records the problem as having progress, without a completed Lean proof. This makes the finite lower bound a documented subresult associated with the catalog problem; it does not establish that formalizing this particular subresult is sufficient for an award.

The proposed role is **formalization contributor**, with mathematical credit retained by the original authors. The [official rules](https://www.hejustinsun.com/prize/rules) distinguish the mathematical solver and Lean formalizer, treat verification as an entry threshold, and leave award assessment to the committees. The completion criteria also exclude work assessed as making no progress. Whether this formalization of an existing finite result qualifies must therefore remain an organizer determination. No award tier, amount, recipient status, or automatic entitlement is asserted.

## Limits

This does not prove `N_{≥7} = 30`, improve the numerical lower bound, or resolve the asymptotic questions in Erdős 82. It does not determine award eligibility or priority. Official designated verification, attribution review, and award assessment remain the organizer's responsibility.

Successful local Lean compilation, fresh kernel replay, independent checking, and repository CI are distinct checks. In particular, repository CI checks record structure and links; it does not by itself execute or approve the mathematical proof. The included local reproduction evidence records toolchain and source hashes, cache use, and actual isolation conditions. It is not an official designated verifier's signed assessment.

## Prior-art screening

A full public REST inventory taken at **2026-09-16 17:51:25 UTC** contained **168 official issues and PRs**. The target-specific search identified the [existing proposal #51](https://github.com/TheJustinSunPrize/awards/issues/51), which is acknowledged, and the older [batch registration issue #24](https://github.com/TheJustinSunPrize/awards/issues/24). The reviewed Issue #51 was posted by `randyxian08` and expressly reported source review only, with no selected or independently checked witness and no completed Lean proof. Its idea and scope precede this candidate package. No claim of originating that proposal, exclusive reservation, or official endorsement is made here.

No completed submission for the 29-vertex witness was located in that snapshot. A previously checked plby file tree had no `Erdos82.lean` entry. A subsequent bounded search used six public queries:

1. `"Erdos82" Lean`
2. `"regular induced subgraphs" "Lean"`
3. `"Dyson" "McKay" "Lean" "29"`
4. `"Pair-Trace Absorption Certificates for Regular Induced Subgraphs"`
5. `"Lean" "regular induced" "29"`
6. `site:github.com "Erdos82" "theorem"`

The relevant source files and paper were then inspected:

- [DeepMind's `formal-conjectures/82.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/82.lean) contains problem and asymptotic-bound statements with `sorry`, not the 29-vertex witness proof. The directly retrieved file SHA-256 was `3fce8571205ae8828c9f102290b7aaacceaaadedaf99efbda9a87373c5d99bcf`.
- [LeanGenius's `Erdos82Problem.lean`](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos82Problem.lean) assumes its stated general bounds as axioms and combines them in a summary theorem; it does not supply this witness. The retrieved file SHA-256 was `c65f00978224f05e748bbe852d8adc57c2ee89a1c6d8739544a69dae32f076e6`.
- [*Pair-Trace Absorption Certificates for Regular Induced Subgraphs*](https://arxiv.org/html/2604.23882) concerns local modular absorption certificates. The inspected paper supplies neither a matching 29-vertex Lean proof nor a linked Lean implementation. Its stated scope differs from this finite witness verification.

No completed matching Lean formalization was located in these checks. Search indexing is incomplete, the source links above are mutable branches, and unpublished or newly released work may be missed. This is **not a global priority guarantee** or a claim that the field is unoccupied.

## Local verification evidence

The [verification record](verification/verification.json), [compilation receipt](verification/compile-build.json), [axiom audit](verification/axiom-audit.log), and [Nanoda output](verification/nanoda.stdout.log) record successful checking of the exact target theorem closures. All 40 local modules compiled successfully; fresh Lean kernel replay, theorem export, and Nanoda each returned exit code 0. Nanoda checked 108,865 declarations without errors, with only `propext`, `Quot.sound`, and `Classical.choice` in the axiom closure. [Negative controls](verification/negative-controls.json) confirm rejection of false cutoff and forged checkpoint certificates.

The verification runner reused the just-completed compiled objects only after validating their source and object hashes against the actual build receipt. Fresh kernel replay and independent checking were executed separately. Network denial passed its control comparison; the filesystem was not isolated and dependencies were drawn from a precompiled cache. [README.md](README.md) gives timings, export identity, and reproduction instructions. These results establish the recorded local verification outcome, while official review remains outstanding.

A final prepublication refresh at 2026-09-16T18:17:28Z covered 176 official issues and PRs. The same related records (#51 and the older aggregate #24) were found; no completed matching PR was located. Details are in `supporting-computation/prior-art-scope.json`.
