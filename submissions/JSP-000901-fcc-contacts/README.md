# Explicit FCC contact configurations in three-dimensional Euclidean space

This Lean 4 project formalizes the classical face-centred cubic (FCC) construction associated with [Erdős problem 1084](https://www.erdosproblems.com/1084), catalogued as JSP-000901. It constructs actual points in `EuclideanSpace ℝ (Fin 3)`, proves their separation, and counts their unordered unit-distance contacts.

For every natural number `m`, the construction has exactly

\[
N_m=4m^3,\qquad E_m=6m(2m-1)^2
\]

points and unordered contacts, respectively. Distinct points have distance at least one. For `m = 0`, the configuration is empty; natural subtraction in the Lean expression `2*m-1` is truncated at zero. For positive `m`, the contact count is also `6*N_m - 24*m^2 + 6*m`.

An additional `q` points may be placed on the first coordinate axis, beyond the FCC box, to obtain exactly `4*m^3+q` points with the same contact count. Distances involving these added points are at least two, so they are isolated in the unit-distance graph.

The final theorem `FCC.all_cardinalities` proves that, for every natural number
`n ≥ 4`, there is an injectively indexed configuration of exactly `n` points in
three-dimensional Euclidean space, with distinct points separated by at least
one, whose number `E` of unordered unit-distance contacts satisfies

\[
E\ \ge\ 6n-200n^{2/3}.
\]

The constant `200` is explicit and nonoptimal. The count is the edge-finset
cardinality of the graph defined directly by Euclidean distance one.

## Scope and status

The mathematical construction is classical. The contribution sought here is an explicit Lean proof of the construction, its Euclidean geometry, its exact contact count, and the all-`n ≥ 4` lower bound obtained by isolated-point padding. This is a lower-bound component of the three-dimensional problem. It does not prove a universal upper bound, the Bezdek--Reid theorem, or the full two-sided asymptotic statement.

The full package, including `FCC.Bounds` and the root module, passed a strict
build with warnings treated as errors. The 20-declaration axiom audit and the
same-kernel replay of all nine local modules also exited successfully. The audit
reported only Lean's standard foundational axioms `propext`, `Classical.choice`,
and `Quot.sound`. The actual logs and result record are in `verification/`.
No award, formal acceptance, global priority, or first-formalization status is asserted.
See [SOURCE_COMPARISON.md](SOURCE_COMPARISON.md) for the precise prior-source
comparison, including the different threshold and configuration encoding of
the reviewed external axiom.

## Main definitions and declarations

| File | Relevant declarations | Meaning |
| --- | --- | --- |
| `FCC/Basic.lean` | `Vertex`, `coord`, `point`, `vertex_card` | Four parity classes in a box, scaled into genuine three-dimensional Euclidean space; cardinality `4*m^3`. |
| `FCC/Geometry.lean` | `point_injective`, `point_separated`, `point_dist_eq_one_iff`, `Contact.offset_ne` | The points are distinct and separated; integer squared distance two is equivalent to Euclidean distance one; every contact joins different parity classes. |
| `FCC/CountCore.lean` | `step_count`, `step_flip_count`, `product_relation_count` | One-dimensional boundary counts and their Cartesian-product factorization. |
| `FCC/Counting.lean` | `classPairCount_01` through `classPairCount_23`, `contactPairs_card` | Each of the six parity-class pairs contributes `m*(2*m-1)^2` contacts. |
| `FCC/Padding.lean` | `paddedPoint_injective`, `paddedPoint_separated`, `paddedPoint_contact_iff`, `paddedPoints_card` | Explicit isolated-point padding, with exact cardinality and no new contacts. |
| `FCC/ContactGraph.lean` | `contactGraph_edge_card`, `paddedContactGraph_edge_card` | The canonical pair count agrees with the edge count of the actual Euclidean unit-distance graph, whose edges are unordered pairs. |
| `FCC/Scale.lean` | `exists_box_scale`, `scale_square_le_rpow`, `contact_count_lower_bound` | An integer box size for every `n ≥ 4`, and the real-power estimate with constant `200`. |
| `FCC/Bounds.lean` | `exact_contacts`, `exact_padded_contacts`, `all_cardinalities` | Exact genuine contact counts and the final configuration theorem for every `n ≥ 4`. |

All declarations above are in the namespace `FCC`. The proof is explained in [PROOF.md](PROOF.md).

## Toolchain and reproduction

The project pins:

- Lean `leanprover/lean4:v4.33.1`;
- Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, selected by the `v4.33.1` dependency and locked in `lake-manifest.json`.

With the pinned Lean toolchain available, run from this directory:

```text
lake exe cache get
lake --wfail build FCC
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker --verbose FCC
```

`--wfail` makes warnings fatal. `Audit.lean` prints the axiom dependencies of 20
key declarations, including the exact counts and final all-cardinality result.
The replay target comprises the root module and all eight local submodules:
`Basic`, `Geometry`, `CountCore`, `Counting`, `Padding`, `ContactGraph`, `Scale`,
and `Bounds`. On Windows, `./verify.ps1` runs these checks and records logs,
versions, and source hashes in `verification/`.

The local dependency cache may be reused through a workspace junction. It and
compiled artifacts are not part of the source deliverable. The checker replay
uses the same Lean kernel implementation and trusts imported dependency caches;
it is not an independently implemented checker, a fresh replay of all Mathlib,
or a network-isolated verification. Actual results belong in the recorded
verification evidence.

Publication preparation keeps the nine proof modules byte-for-byte identical
to their reviewed and verified LF sources. Source hashes were refreshed after
the final documentation update; the already recorded build, axiom audit, and
module replay were retained as their actual executions.

## Attribution and license

The proof code and documentation were developed with OpenAI Codex under the
user's direction. Separate Codex agents contributed proof work and source
review; no human-only authorship or independent human review is claimed. The
public maintainer and submitting account is
[156631890](https://github.com/156631890).

The original source files and documentation are available under
[Apache-2.0](LICENSE). Fetched dependencies retain their respective licenses.
The classical mathematical construction and the reviewed earlier formal source
are credited in [SOURCE_COMPARISON.md](SOURCE_COMPARISON.md).

Kernel checking certifies the formal statements under their reported axioms;
it does not by itself establish novelty, equivalence to every formulation of
the original problem, or prize eligibility.
