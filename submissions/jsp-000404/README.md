# JSP-000404 / Erdős 504: correction and partial Lean formalization

**This is a source correction and partial formalization. The full Sendov classification is not proved in this package.** It does not support changing the catalog's complete-proof or award-eligibility fields.

The [linked Erdős problem page](https://www.erdosproblems.com/504) gives a lower-interval expression that yields `alpha(5) = 4π/5`. We disprove that expression with five explicit planar points in Lean. Sendov's final theorem instead has numerator **2**, yielding `3π/5`. The English paper's introduction also prints numerator 1, whereas its final theorem and the Russian exposition print 2. See [SOURCE_CORRECTION.md](SOURCE_CORRECTION.md) for exact formulas, indices, pages, and primary references.

The Lean proofs in this partial package were jointly completed by [superpilot69](https://github.com/superpilot69), X/Twitter [@wofuhuola](https://x.com/wofuhuola), and ChatGPT 6 Astra. The classical mathematical results remain attributed to Szekeres, Erdős–Szekeres, and Sendov; see [ATTRIBUTION.md](ATTRIBUTION.md).

## Formal statement and checked results

`Point` is Mathlib's real Euclidean plane, `EuclideanSpace ℝ (Fin 2)`. Angles use `EuclideanGeometry.angle`, in radians. `Guaranteed N θ` means that every finite set of exactly N distinct points contains three pairwise distinct points making an angle at least θ. `alpha N` is the supremum of these guaranteed thresholds. For N ≥ 3, `alpha_eq_sInf` proves equivalence to the infimum of the largest angles of all N-point configurations. No general-position restriction is imposed.

The independently checked counterexample is the set

```text
{(-1,-1), (1,-1), (1,1), (0,2), (-1,1)}.
```

Every angle in it is at most `3π/4 < 4π/5`. In particular, `JSP404.not_transcribed_lower_formula` disproves the stated lower-interval formula using genuine Euclidean points. This counterexample does not by itself compute `alpha(5)` exactly.

| Module | Proven scope |
| --- | --- |
| [Basic](JSP404/Basic.lean) | Literal geometric definitions; equivalence with the minimax infimum; monotonicity; epsilon approximation; universal π/3 lower bound. |
| [Counterexample](JSP404/Counterexample.lean), [FormulaCorrection](JSP404/FormulaCorrection.lean) | Rational five-point counterexample and formal refutation of the numerator-1 formula. |
| [BinaryEncoding](JSP404/BinaryEncoding.lean) | Binary separation and weighted counting for bipartite graph covers. |
| [DirectionalCover](JSP404/DirectionalCover.lean), [EquallySpacedDirections](JSP404/EquallySpacedDirections.lean) | Geometric cone coloring and an actual equally spaced direction cover; if k ≥ 2 and N > 2^k, every N-point set has an angle at least `(1−1/k)π`. |
| [BinaryConstruction](JSP404/BinaryConstruction.lean), [ClassicalBounds](JSP404/ClassicalBounds.lean) | Binary configurations built at successively smaller scales; the unconditional classical upper bound `alpha(2^k) ≤ (1−1/k)π` for k ≥ 2 and its cardinality consequences. |
| [HierarchicalConstruction](JSP404/HierarchicalConstruction.lean), [ClusterConstruction](JSP404/ClusterConstruction.lean) | Finite cluster contraction and binary-cluster upper bounds under explicitly stated directional hypotheses. These are reusable construction theorems, not the completed sharp construction for every interval. |
| [ThreeCenterBound](JSP404/ThreeCenterBound.lean) | The three-variable floor/exponent capacity inequalities under normalized angle hypotheses. The reduction of arbitrary planar configurations to these hypotheses is not claimed. |

## Reproduce

Use **Lean 4.34.0**, compiler commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0). Toolchain and all dependency revisions are pinned.

From this directory, with the pinned toolchain installed and Lake on PATH:

```sh
lake exe cache get
python3 scripts/verify.py --clean
```

Alternatively, pass `--lake /path/to/lean-4.34.0/bin/lake`. The standard-library-only Python script checks toolchain and Mathlib revisions, rebuilds this package, audits every named theorem declared in its Lean modules, rejects nonstandard axiom dependencies, and records source hashes. It preserves dependency caches; `--clean` rebuilds this package's proof files rather than rebuilding Mathlib from scratch.

The permitted axiom dependencies are `propext`, `Quot.sound`, and `Classical.choice`. No added mathematical axioms, admitted proofs, or `native_decide` certificates are used. Recorded output is in [verification/result.json](verification/result.json) and [verification/build-and-axioms.log](verification/build-and-axioms.log). This is local Lean compilation and dependency auditing, not an independent external verification or prize decision.

## Remaining work

The complete classification needs the sharp general-center geometric counting argument, its bridge from arbitrary configurations, and the specialized three-center construction for the intermediate interval. The classical binary construction already supplies the other upper-bound branch. The present three-center arithmetic and conditional construction interfaces do not establish the missing general reduction. Subsequent work can extend these modules without assuming Sendov's main theorem as an axiom.
