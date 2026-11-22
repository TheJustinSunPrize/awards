# Proposed catalog addition: Erdős problem 1092

[Problem index](../README.md) · [Recommendation and scope request #5024](https://github.com/TheJustinSunPrize/awards/issues/5024)

This is an **unassigned proposal for maintainer review**, with complete mathematical
and Lean proof evidence. It is not an accepted catalog entry, candidate registration
or award claim. Maintainers are asked to decide inclusion, the final JSP identifier
and catalog location, and the correspondence to the original problem. No new JSP
number is assigned here; the existing 1,022 catalog records and their index remain
unchanged.

## Proposed record

| Field | Proposed content |
| --- | --- |
| Catalog identity | Unassigned — Erdős problem 1092; independent addition requested. |
| Date proposed | Unspecified (to verify). |
| Mathematical area | Graph theory / Chromatic number / Hereditary edge deletion. |
| Problem description | For every fixed integer r ≥ 2, can an admissible natural-valued hereditary edge-deletion budget g have an eventual positive linear lower bound? Here admissible means that every finite graph G has chromatic number at most r+1 whenever every subgraph H of G can be made at most r-colorable by deleting at most g(card V(H)) of its actual edges. All subgraph sizes are tested with the same g, including isolated vertices. The answer is negative for each fixed r ≥ 2. |
| Current status | Solved — negative answer.<br>Mathematical sources: Vojtěch Rödl's 1982 construction; Quanyu Tang's E1092 observation and Przemek Chojecki's all-r clique-join reduction, with the specific roles and references below. No new mathematical solver contribution is claimed in this proposal. |
| Lean proof | Yes — complete source supplied for review: [Erdos1092.erdos_1092](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/Erdos1092/Main.lean#L43), in the original [Wang060919/erdos1092-lean](https://github.com/Wang060919/erdos1092-lean) repository, branch main, commit 7649a561f6c2c8caabd60d0834beeffe89a357d5.<br>Requested display credit: Wang060919, using the repository-owner attribution convention; authorship and priority remain subject to review. |
| Attribution basis | Mathematical publication identity and publicly attributed observations: [Rödl publication](https://doi.org/10.1007/BF02579434), [Tang](https://www.erdosproblems.com/forum/thread/1092#post-1675), [Chojecki](https://www.erdosproblems.com/forum/thread/1092#post-5983). [Bloom's at-most-r clarification](https://www.erdosproblems.com/forum/thread/1092#post-6408) establishes the coloring convention used in the statement.<br>Lean: [attribution conventions](../README.md#attribution-conventions), [original repository provenance](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/ATTRIBUTION.md), and the fixed proof source above. Ownership does not establish sole manual authorship or award eligibility. |
| Eligible to claim | Pending verification — inclusion, mathematical review, statement correspondence, formalization verification and attribution require maintainer review. No candidate or award record is proposed. |
| Historical bounty | Not recorded in this proposal. |
| Elapsed years | Not assessed; the original problem date is unconfirmed. |
| Publication details | *Nearly bipartite graphs with large chromatic number*, Combinatorica 2, 377–383 (1982), [DOI 10.1007/BF02579434](https://doi.org/10.1007/BF02579434). Publication metadata and abstract were inspected, rather than the complete seven-page paper.<br>A complete self-contained proof for the exact scope is supplied independently of access to that paper: [mathematical proof, Sections 1–4](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/MATHEMATICAL-PROOF.md). It is an exposition of the already solved mathematics, not a new-solver claim. |
| Scholarly recognition | The journal publication is listed above. No separate award, independent human verification, or organizer approval is claimed. |

## Exact scope and correspondence

The [original problem](https://www.erdosproblems.com/1092) and the
[canonical all-subgraph statement](https://github.com/google-deepmind/formal-conjectures/blob/34ee0e3c5fd52d202d62a71094a37970cb5fb870/FormalConjectures/ErdosProblems/1092.lean)
use a budget evaluated at each subgraph's own vertex count. Subgraphs need not
be induced and may omit arbitrary vertices and edges. The condition includes
all sizes simultaneously, with no monotonicity assumption on g. The deleted
set consists of actual edges of H, rather than vertices or ambient edges absent
from H.

The endpoint has only r and 2 ≤ r as arguments. For every fixed r ≥ 2 it negates
existence of an admissible g satisfying n = O(g(n)), equivalently an eventual
bound g(n) ≥ cn for some c > 0. It does not assert the stronger conclusion
that every admissible g is o(n). The construction, hereditary edge cuts, clique
join, small-size integrality argument and asymptotic bridge are all proved;
no core-existence hypothesis remains at the final theorem.

The [scope audit](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/docs/SCOPE.md)
and [independent literal statement check](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/CheckScope.lean)
provide the exact definitions and bridges. This is distinct from E74/JSP-000091;
a shared Rödl reference does not identify the two problem scopes.

## Reproduction and review evidence

- Lean: leanprover/lean4:v4.33.0, release commit d8b18978322de05a8f3dba51ef03cf5461676c17.
- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency revisions are fixed in the [Lake manifest](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/lake-manifest.json).
- [Setup and commands](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/README.md): use the pinned toolchain, then run ./scripts/cache.sh and ./scripts/verify.sh in the external proof repository.
- [Clean independent-directory reproduction](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/portable-reproduction.json): no copied project .lake or custom proof artifacts, freshly fetched exact dependency sources, fresh custom builds, and official compiled-library caches.
- [Public CI run 38265286397](https://github.com/Wang060919/erdos1092-lean/actions/runs/38265286397) completed successfully with head_sha exactly 7649a561f6c2c8caabd60d0834beeffe89a357d5. It checks source hashes and actual dependency revisions, builds with Lean warnings treated as failures, elaborates four literal bridges, audits all 68 public declarations and kernel-replays all seven custom proof modules.
- [Actual axiom queries](https://github.com/Wang060919/erdos1092-lean/blob/7649a561f6c2c8caabd60d0834beeffe89a357d5/verification/CheckAxioms.lean): only propext, Classical.choice and Quot.sound occur at the four final endpoints. All queried declarations and literal bridges use these standard foundations or subsets, with no custom unproved axiom.

Imported pinned Mathlib/dependency libraries are trusted, rather than all
independently replayed. No separate external checker or independent human
verifier is claimed. The mathematical solution and formalization require
separate organizer review; compiler success does not replace mathematical review.

## Related records and conflicts

The 2026-10-12 audit inspected open, closed and merged proof records, public
claims, GitHub Lean repositories and batch formalizations. No earlier complete
effective Lean proof of this exact scope was confirmed in the inspected sources;
this is a bounded search conclusion, not a global absence or earliest-priority
claim. The linked scope audit records the actual statement gaps: plby's E1092
uses one fixed subgraph size, lean-genius PR 43572 uses a uniform budget for a
fixed ambient order, canonical Formal Conjectures endpoints remain unfinished
in the inspected snapshot, and E750's vertex cuts do not supply the required
hereditary small edge cuts.

Relevant public professional relationships: none, as confirmed by the publisher.
The [recommendation issue #5024](https://github.com/TheJustinSunPrize/awards/issues/5024)
is the same E1092 proposal; this PR supplies its reviewable record and complete
proof references, rather than creating another recommendation or award claim.
