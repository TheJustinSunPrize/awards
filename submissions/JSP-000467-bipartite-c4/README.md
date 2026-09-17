# Exact four-cycle packing in complete bipartite graphs

This Lean 4 project proves the exact maximum number of vertex-disjoint ordinary
four-cycles in every complete bipartite graph:

\[
\nu_{C_4}(K_{a,b})=\min(\lfloor a/2\rfloor,\lfloor b/2\rfloor).
\]

The proof applies to arbitrary packings and constructs a packing attaining the
bound. It includes empty classes and the empty packing. A cycle is an injective
copy of Mathlib's `cycleGraph 4`; the cycles are not required to be induced.

For every integer `k > 0`, it follows that `K_(2k-1,2k+1)` has `4k` vertices,
minimum degree `2k-1`, and exact packing capacity `k-1`. Thus the minimum-degree
threshold `2k` in Wang's solution of **Erdos problem 577 / JSP-000467** cannot be
reduced by one. The witnesses have arbitrarily large order.

This is an incremental formalization of a classical exact construction and
sharpness argument. It does not prove Wang's positive threshold theorem, claim
new mathematics, or establish global priority for its formalization.

## Main declarations

- `BipartiteC4.Packing.cycle`: each packing member is a genuine Mathlib C4 copy.
- `BipartiteC4.Packing.disjoint_cycles`: different copies have disjoint vertices.
- `BipartiteC4.Packing.left_bound` and `right_bound`: every packing uses at least
  two vertices per cycle on each side.
- `BipartiteC4.canonicalPacking`: explicit construction of every feasible size.
- `BipartiteC4.hasPacking_iff`: feasibility iff `2*k <= a` and `2*k <= b`.
- `BipartiteC4.exact_capacity` and `maximum_attained`: exact formula and attainment.
- `BipartiteC4.sharpness`: the entire minimum-degree obstruction family.
- `BipartiteC4.necessary_degree_threshold`: every universal threshold is at least
  `2*k` for positive k.
- `BipartiteC4.arbitrarily_large_sharpness`: witnesses beyond any size bound.

## Reproduction

Lean: `v4.33.1`. Mathlib: `v4.33.1`, commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
lake exe cache get
lake --wfail build BipartiteC4
lake env lean -DwarningAsError=true Audit.lean
```

On Windows, `./verify.ps1` also checks the local sources for proof escapes,
replays all five local modules with `leanchecker`, and records logs, exact tool
versions, and SHA-256 hashes under `verification/`. The replay uses the same Lean
kernel implementation and trusts the imported dependency caches; it is not a
fresh replay of every Mathlib dependency or an independently implemented checker.

The local workspace reuses a dependency-cache junction. The junction and compiled
artifacts are not part of the source deliverable. A fresh checkout obtains the
pinned dependencies from `lake-manifest.json`.

See `PROOF.md` for the mathematical argument, `SOURCE_COMPARISON.md` for the
bounded comparison with prior public formalization, and `verification/` for the
actual build and axiom evidence. No remote submission is performed by these files.

## Sources and attribution

- [Erdos problem 577](https://www.erdosproblems.com/577).
- Hong Wang, *Proof of the Erdos-Faudree Conjecture on Quadrilaterals*, Graphs and
  Combinatorics 26 (2010), 833-877,
  [DOI:10.1007/s00373-010-0948-3](https://doi.org/10.1007/s00373-010-0948-3).
- [JSP-000467](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000467).
- Mathlib's definitions of complete bipartite graphs, cycle graphs, and graph copies.

The graph-copy definition was cross-checked against the public Erdos577 packing
definition listed in `SOURCE_COMPARISON.md`. The exact bipartite-capacity theorem
and the explicit sharpness family are the scope of this project.

The proof code and documentation were developed with OpenAI Codex under the
user's direction. Separate Codex agents performed proof construction and source
review; this is not a claim of independent human review. The public maintainer
and submitting account is [156631890](https://github.com/156631890).

The original source files and documentation in this repository are available
under [Apache-2.0](LICENSE); see [NOTICE](NOTICE) for attribution. Dependency
licenses remain with their respective projects.

For publication, text files are normalized to LF line endings. The five proof
modules are unchanged except for line-ending normalization. Their published
byte hashes replace the pre-normalization hashes in `statement-review.md`;
`verification/normalization.json` preserves both sets. The existing build,
axiom-audit, and replay results were retained rather than represented as newly
run checks. The published file manifest describes the normalized source bytes.
