# JSP-000895 / Erdős 1076: finite upper bound under the single (5,3) prohibition

**Proposed classification: Partial Progress. Official intake and review are pending.**

For every finite simple three-uniform hypergraph `G` on `n` vertices, if any three distinct edges together span more than five vertices, then

`5 * G.card <= 2 * n.choose 2`.

Equivalently, `|G| <= n(n-1)/5`. The same bound is proved for the corresponding finite extremal function. The only forbidden-configuration assumption is `FkFree 5`; no linearity or `FkFree 4` assumption is added.

The main targets in `JSP000895.FiveThreeUpper` are:

- `Erdos1076Upper.five_mul_card_le_two_choose`;
- `Erdos1076Upper.five_mul_extremalNumber_five_le_two_choose`.

This is a new formal implementation of a known finite upper bound due to Stefan Glock. It is not a new mathematical discovery, a matching asymptotic lower bound, a limit theorem, or a solution of every `k` case. See [SCOPE.md](SCOPE.md) for the exact assumptions and small-order convention.

## Proof and existing work

The proof counts the two-element shadow of the edge family. Each isolated edge uses three pairs; two edges sharing a pair use five pairs. Freeness forces those five pairs to be unused by all remaining edges. Strong induction deleting one or two edges proves `5 * |G| <= 2 * |shadow G|`. The shadow is contained in the `n.choose 2` vertex pairs. A finite-supremum argument then gives the extremal-function target.

The six minimal model definitions are reproduced in a separate namespace from the attributed Apache-2.0 source in [source-origin.json](source-origin.json); their source bodies were compared with the pinned original. The upper-bound proofs are newly written. The large existing lower-bound construction is not imported.

[PR90](https://github.com/TheJustinSunPrize/awards/pull/90), reviewed at head `983a20fcb5f44fa72c3c279e065546a14640784f`, addresses a cumulative forbidden family whose upper bound assumes `FkFree 4`. That stronger assumption excludes intersecting edges sharing a pair. This package allows such edge pairs and proves a different constant under only `FkFree 5`. It does not rebrand the existing cumulative-family theorem as a new result. [PROVENANCE.md](PROVENANCE.md) records the mathematical source, license and bounded duplicate review.

## Reproduction

The package uses Lean 4.33.0 (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Dependency revisions are pinned in `lake-manifest.json`.

With an existing compiled checkout of that exact Mathlib pin and its dependency caches, run:

```text
python reproduce.py --lean-bin /path/to/lean-4.33.0/bin --mathlib-dir /path/to/mathlib
```

Quote paths containing spaces on Windows. The helper rebuilds both package modules into fresh outputs, prints the two target axiom sets, and replays each module with an exact module-list check. It fixes the sysroot and thread count and checks source and existing custom-artifact stability. It does not modify the supplied toolchain or Mathlib. Coordinate any shared-machine Lean mutex outside the helper.

The ordinary Lake configuration is also provided:

```text
lake exe cache get
lake build JSP000895
lake env leanchecker --verbose JSP000895.FiveThreeUpper
lake env leanchecker --verbose JSP000895.Audit
```

The public helper was actually run on Windows from this package. Both modules compiled into fresh outputs, both exact-module kernel replays passed, and both target axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. The four process steps and exact source/helper/tool hashes are recorded in [evidence/verification.json](evidence/verification.json); see [source-manifest.json](source-manifest.json). The full fresh run, rather than an earlier development compile, is the submitted execution evidence. Existing Mathlib binaries are the imported trust boundary. A full dependency rebuild, network-disabled isolation, an independently implemented checker, or organizer certification is not claimed. `leanchecker` uses the same Lean kernel.

## Attribution and intake

Prepared with OpenAI Codex assistance. Mathematics is attributed to Glock; the copied definitions retain the upstream source's notices and author credits. The new proof and its adaptation are identified explicitly. See [NOTICE](NOTICE) and [LICENSE](LICENSE).

Proposed recipient placeholder: `RECIPIENT-JSP-000895-A`, confirmation pending. The submitting effort has a direct interest in review. Attribution does not nominate another author or assert their endorsement.

This is a proposed proof-intake package under `submissions/`. It changes no catalog flags, candidate or award records, recipient profiles, official signatures, decisions or payment statuses. Statement review, independent verification, archival requirements, eligibility, acceptance and any award remain for the organizer.
