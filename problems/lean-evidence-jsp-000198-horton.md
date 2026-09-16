# JSP-000198: Lean evidence for the Horton component

## Scope

This submission covers **Horton's result for k >= 7**, a component of
[JSP-000198](catalog-0101-0200.md#JSP-000198), corresponding to
[Erdős problem 216](https://www.erdosproblems.com/216).

For every natural number N and every k >= 7, there exists a set of **exactly N
integer-coordinate points** in the real plane, no three distinct points
collinear, with no empty convex k-gon. This excludes a finite forcing threshold
for all k >= 7. The finite threshold claims for k = 3, 4, 5, and 6 are outside
this submission. Completion of this component does not establish complete Lean
coverage of the combined catalog entry.

## Source and attribution

The mathematical construction and nonexistence result are due to **J. D. Horton**,
*Sets with No Empty Convex 7-Gons*, Canadian Mathematical Bulletin 26(4),
482–484 (1983), [DOI](https://doi.org/10.4153/CMB-1983-077-8).
The [original technical report](https://unbscholar.lib.unb.ca/items/305fcc21-8cce-4120-bd11-c49af7397388)
provides another source for the mathematical argument.

The [pinned Lean source](https://github.com/tester-lean/jsp-000198-horton-lean/tree/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0) is a new implementation against mathlib,
developed with Codex assistance. The contribution being submitted is
formalization and verification of this known result. No first-publication
priority or new mathematical solution is claimed. No EmptyHexagonLean code is
imported. The source and theorem export retain the applicable third-party
library licenses.

## Formal statements and definition correspondence

[Main theorem file](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/Prize/Horton.lean):

- `Prize.Horton.horton_no_empty_seven`: exactly N integer-coordinate points in
  general position with no empty convex seven-gon, for every N.
- `Prize.Horton.horton_no_empty_k_gon`: the same conclusion for each k >= 7.
- `Prize.Horton.no_finite_threshold`: no finite threshold forces an empty convex
  k-gon for k >= 7.

[Definitions](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/Prize/Geometry/EmptyPolygon.lean):

| Mathematical concept | Formal representation |
| --- | --- |
| Real plane | `Point := ℝ × ℝ` with its usual vector-space and product-topology structures. |
| Finite point set and its size | `Finset Point` and `Finset.card`. |
| General position | Every three pairwise distinct members are not `Collinear ℝ`. |
| Convex polygon vertices | mathlib `ConvexIndependent ℝ` on the vertex subtype. |
| Empty interior | An ambient point in `interior (convexHull ℝ S)` must belong to S; convex independence excludes the vertices themselves from the polygon interior. |
| A k-gon | A vertex subset of cardinality k satisfying those convexity and emptiness conditions. |
| Integer coordinates | Explicit existential witnesses in `ℤ` for both real coordinates. |

The proof constructs recursively separated even/odd subsequences. Visibility
bounds limit an empty polygon meeting both subsequences to three vertices in
each; a polygon confined to one subsequence reduces recursively. An initial
segment in increasing horizontal order yields exactly N points, while removed
points cannot lie inside its convex hull. Convex vertex subsets yield the
k >= 7 corollary. Selecting integer vertical shifts uses classical choice;
this formalization does not provide an executable coordinate generator.

## Reproduction and axiom audit

- Proof commit: `313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0`.
- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Other dependencies are fixed in `lake-manifest.json`.

```sh
lake exe cache get
lake build Prize.Horton Prize.Audit
lake env lean Prize/Audit.lean
```

All three final theorems have precisely the standard axiom dependencies
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom mathematical
axioms, SAT assumptions, or native-evaluation axioms occur in these dependencies.
See the [actual axiom output](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/verification/horton-axioms.txt).

A [separate rebuild](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/verification/clean-build.log) passed in a
network-disabled user/network namespace, without reusing project `.olean` files.
It reused pinned upstream dependency artifacts. The run used an unprivileged
host user, a 600-second timeout, and a 32-GiB per-process virtual-memory limit.

**nanoda 0.4.17** independently checked the exported closure of all three final
theorems: **19,589 declarations with no errors**, allowing only the same three
axioms. The [checker output](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/verification/nanoda.log),
[strict configuration](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/verification/nanoda-config.json), and
[metadata](https://github.com/tester-lean/jsp-000198-horton-lean/blob/313363e3613d0bc1ce1ad2ba7a8e7d26b1645fd0/verification/metadata.json) are available at the pinned source.
The Lean exporter was built at `fd0d78eaa91750096cf519907b266efb1b26bf22`, with
its toolchain file overridden to Lean 4.34.0. nanoda was built at
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. The repository includes a script to
reproduce the export and external type check from those revisions.

The submitter ran both checks. Independent human definition/statement review
and any committee verification remain pending.

## Archived artifacts

[Evidence archive](https://github.com/tester-lean/jsp-000198-horton-lean/releases/download/v0.1.0/horton-evidence-v0.1.0.tar.gz)
([release page](https://github.com/tester-lean/jsp-000198-horton-lean/releases/tag/v0.1.0)):

- Archive ID: `tester-lean/jsp-000198-horton-lean@v0.1.0/horton-evidence-v0.1.0.tar.gz`.
- SHA-256: `96042fc36516ebc453e32db4c31163bd4161c9d3ab6cf44dac78c84cf1773bb6`.
- Bytes: `15903288`.

The archive contains the source at the pinned commit, the theorem export,
reproduction configuration, build/axiom/checker logs, and third-party licenses.
The uncompressed export is 97,244,039 bytes, with SHA-256
`50b6ae8709c697319dc67aa8d886bd9155443dba13f6ba96bbcced1bf5d35265`.

## Review and record status

This is submitter-provided evidence for a complete component theorem. The
catalog's Lean field should record partial coverage of the combined entry.
The existing eligibility marker does not change on the basis of this submission.
No candidate verification decision, confirmed recipient identity, award level,
or payment decision is asserted. Any recipient recommendation uses a placeholder
pending the required confirmation.
