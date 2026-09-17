# JSP-000895 / Erdős 1076: two finite upper bounds

**Proposed classification: Partial Progress. Official intake and review are pending.**

This package gives new Lean implementations of two known finite bounds for simple three-uniform hypergraphs `G` on `n` vertices:

| Assumptions | Finite conclusion |
|---|---|
| Only `FkFree 5 G` | `5 * G.card <= 2 * n.choose 2` |
| `FkFree 5 G` and `FkFree 6 G` | `3 * G.card <= n.choose 2` |

The first is also proved for the single-F5 finite extremal function. The second is a graph theorem, with its forbidden-configuration contrapositive; it is not asserted for the existing single-Fk extremal function. Neither proof assumes `FkFree 4` or linearity. The all-n at-most-k convention and the exact-vertex wording are distinguished in [SCOPE.md](SCOPE.md).

The terminal targets are:

- `Erdos1076Upper.five_mul_card_le_two_choose`;
- `Erdos1076Upper.five_mul_extremalNumber_five_le_two_choose`;
- `Erdos1076Upper.three_mul_card_le_choose_of_five_six`;
- `Erdos1076Upper.not_five_free_or_not_six_free_of_choose_lt_three_mul_card`.

These formalize known mathematics explained in Stefan Glock's paper. Matching lower bounds, normalized limits and the general k problem are not proved here. No mathematical discovery or global first-formalization priority is claimed.

## Proofs and existing work

The single-F5 proof counts the ordinary two-element shadow. An isolated edge needs three pairs; two edges sharing a pair need five pairs. Freeness forces those resources to be unused by remaining edges. Deletion induction proves the shadow bound, followed by the ambient pair count and a finite supremum argument.

The F5-and-F6 proof completes the shadow on each overlapping pair of edges to all six pairs on its four vertices. F5 separates such a block from remaining single edges. F6 separates two blocks: a shared pair would put four distinct edges on at most six vertices. Deleting one or two edges therefore charges three or six disjoint pairs. The four-edge distinctness is proved explicitly from deletion membership. The stronger resource inequality is also audited.

Six minimal model definitions retain the notices of the Apache-2.0 source identified in [source-origin.json](source-origin.json). Both upper proofs are newly written and import only Mathlib and this package's own prior module; the existing large lower construction is not imported. [PR90](https://github.com/TheJustinSunPrize/awards/pull/90), reviewed at `983a20fcb5f44fa72c3c279e065546a14640784f`, uses `FkFree 4` in its upper bound. The two-edge family `{123,124}` satisfies both present freeness assumptions but is not F4-free, illustrating the difference. See [PROVENANCE.md](PROVENANCE.md).

## Reproduction and evidence

Use Lean 4.33.0 (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) and an existing compiled Mathlib checkout at `db584cd6d46c92f209a44c0f1c829460d327499d` with its pinned dependency caches:

```text
python reproduce.py --lean-bin /path/to/lean-4.33.0/bin --mathlib-dir /path/to/mathlib
```

Quote paths containing spaces. The actual final public helper rebuilt all three modules into fresh outputs and completed all three exact-module replays. All six process steps passed; five named target-axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. Exact source/helper/tool identities, log hashes and actual results are in [evidence/verification.json](evidence/verification.json) and [source-manifest.json](source-manifest.json).

The helper removes inherited Lean/Lake environment variables, fixes the sysroot and thread count, excludes the source root from the module search path, verifies revisions, and checks source, custom artifacts, control files and tool identities. Coordinate any shared-machine Lean mutex outside the helper. Existing Mathlib/dependency binaries remain a disclosed trust boundary: no full dependency rebuild, network-disabled run, independently implemented checker or organizer certification is claimed. `leanchecker` uses the same Lean kernel. Semantic reviews are contributor-side AI reviews.

The ordinary Lake route is also configured:

```text
lake exe cache get
lake build JSP000895
lake env leanchecker --verbose JSP000895.FiveThreeUpper
lake env leanchecker --verbose JSP000895.FiveSixUpper
lake env leanchecker --verbose JSP000895.Audit
```

The original single-F5 source, two-module evidence and archive remain available at [commit d374810](https://github.com/zifanersuotang/awards/tree/d374810e3ddd909e41e297bef177e9da35357303/submissions/jsp-000895) and [its release](https://github.com/zifanersuotang/awards/releases/tag/jsp-000895-finite-upper-2026-09-17). Copies of that historical evidence and its manifest are under `evidence/single-f5-2026-09-17/`; the historical manifest identifies the original package, not the current helper or Audit. The original `FiveThreeUpper.lean` is unchanged. Current execution claims use the new six-step record, not the earlier development runs or the pre-clarification comment revision.

## Attribution and intake

Prepared with OpenAI Codex assistance. Mathematics is attributed to the cited literature; copied definitions retain their upstream notices and authors. See [NOTICE](NOTICE) and [LICENSE](LICENSE). Proposed recipient placeholder: `RECIPIENT-JSP-000895-A`, confirmation pending. The submitting effort has a direct interest in review. Attribution is not an endorsement or nomination on another author's behalf.

This proposed intake package changes no catalog flags, candidate or award records, recipient profiles, signatures, decisions or payment statuses. Statement review, independent verification, archive requirements, eligibility, acceptance and any award remain for the organizer.
