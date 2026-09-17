# Mathematical provenance and comparison with reviewed formal sources

Review date: 2026-09-17. This document describes the sources actually inspected. It is not a claim of an exhaustive global search or first publication.

## Original mathematical problem and scope

- Original problem page: [Erdős problem 1084](https://www.erdosproblems.com/1084).
- Associated prize catalog entry: JSP-000901.
- The relevant extremal quantity counts the largest possible number of unordered unit-distance pairs in a configuration of `n` points whose distinct points are separated by at least one.

The FCC lattice is classical: it consists of integer triples with even coordinate sum, scaled by `1/sqrt(2)`. Finite clusters give the standard three-dimensional lower-bound order `6n - O(n^(2/3))`. This project does not claim that the lattice, the construction method, or that asymptotic lower bound is new mathematics.

The scope of this package is the explicit FCC lower-bound construction,
including its exact finite counts and the resulting existence theorem with at
least `6n-200n^(2/3)` contacts for every `n≥4`. A two-sided statement such as
`6n - Θ(n^(2/3))` additionally needs an upper bound that holds for every separated
configuration. The Bezdek--Reid upper bound is not proved here.

## A concrete gap in one reviewed Lean source

The following file was read at a fixed commit:

- Repository: `rjwalters/lean-genius`.
- Commit: `dc62f771ed5010abfdb04247dff6143e0e69d3e7`.
- File: [`proofs/Proofs/Erdos1084OQ01.lean`](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1084OQ01.lean).

At [lines 580--584](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1084OQ01.lean#L580-L584), it declares:

```lean
axiom fcc_cluster_pairs :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    ∃ C : SepConfig 3 n,
      (unitPairs C : ℝ) ≥ 6 * n - c * (n : ℝ) ^ (2/3 : ℝ)
```

This is an assumed declaration, not a Lean proof of the FCC construction. The file explicitly lists that lower bound among its remaining axioms. It separately declares the Bezdek--Reid upper bound as an axiom at lines 590--595. The later combined asymptotic theorem must therefore be assessed with those assumptions visible.

This observation concerns this particular file at this particular commit. It is not a finding that all other proofs in that repository are unverified, nor that no complete formal proof exists elsewhere. The reviewed external file was inspected for scope and assumptions; this comparison does not assert that we independently rebuilt it.

## What the present package contributes

| Component | Reviewed external source | Present package |
| --- | --- | --- |
| Ambient geometry | `SepConfig` uses real Euclidean space. | `FCC.point` explicitly constructs points in `EuclideanSpace ℝ (Fin 3)`. |
| Separation of FCC points | The FCC existence bound is assumed. | Integer parity, coordinate injectivity, and the exact scaled distance identity establish separation. |
| Finite FCC contact count | No exact finite FCC box construction occurs in the cited axiom. | The four parity classes give `4m³` points and six exact contributions of `m(2m-1)²` contacts. |
| Unordered geometric pairs | `unitPairs` uses ordered indices to choose one orientation. | A Euclidean `SimpleGraph` and `Sym2` edges are proved to agree with the canonical parity-class orientation. |
| Arbitrary larger cardinality | Included in the assumed lower-bound assertion. | Explicit far-away points preserve the contact count, with a proved exact cardinality. |
| All-size asymptotic lower bound | Assumed for every `n≥2`, with an existential positive constant. | `FCC.all_cardinalities` constructs configurations for every `n≥4`, with the explicit nonoptimal constant `200`. |
| Universal upper bound | `bezdek_reid` is a separate axiom. | Outside this package's scope. |

The new Lean modules do not import the reviewed file or use its
`fcc_cluster_pairs` or `bezdek_reid` declarations. They are independently written
formal proofs of the finite construction, padding, and all-`n≥4` lower bound.
The final package audit, rather than this comparison table, is the authority for
their actual axiom dependencies.

The completed local verification recorded exit code zero for the strict build,
the 20-declaration axiom audit, and the replay of all nine local proof modules.
The audit found only `propext`, `Classical.choice`, and `Quot.sound`. This provides
checked proof evidence for the declarations of this package under the disclosed
trust boundary; it does not establish worldwide formalization priority.

The exact-family theorem alone would not imply the all-size assertion. This
package additionally proves padding, preserves genuine unordered contact
counts, and chooses a box size for every `n≥4`. Its final theorem and the cited
axiom still have different thresholds and encodings: the external statement
starts at `n≥2` and uses `SepConfig` on `Fin n`, while the new theorem starts at
`n≥4` and uses an injective Euclidean map on an index type proved to have
cardinality `n`. No direct Lean conversion to that external `SepConfig`, nor a
literal replacement declaration in that repository, is provided. This is an
explicit proof of the relevant asymptotic lower-bound component, with those
differences disclosed.

## Other search evidence and its limits

The official awards repository was searched for PRs using `1084`, `000901`, and
`FCC`. The first two searches returned [PR #275](https://github.com/TheJustinSunPrize/awards/pull/275);
the `FCC` search returned no matches. The PR description at head commit
`c24b0b9045f43b04d08a3e3dbb55cea402ac8654` explicitly scopes that submission to the
one-dimensional formula `f₁(n)=n-1` and states that the three-dimensional bounds
are not formalized or claimed. It is therefore a relevant earlier scoped
submission for the same catalog entry, with a different stated mathematical
component. This comparison uses the PR's actual description; it does not claim
that we independently audited or rebuilt that submission. Keyword searches are
not exhaustive, and an open community PR is not an award decision.

The reviewed main-file index of `plby/lean-proofs` at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` did not list a main file for Erdős 1084. This is only a bounded negative search result. It does not exclude differently named files, later changes, unpublished work, or formalizations in other repositories.

The official awards repository, current submissions, and external proof repositories may change after this review. A public priority or award request should identify the published immutable source commit and compare against the then-current relevant submissions. Passing the Lean kernel checks is evidence of the encoded statements; award eligibility and priority remain matters for the actual review process.

## Attribution and assistance

The underlying FCC construction and the broader contact-number problem belong to the mathematical literature. The reviewed `lean-genius` source is credited for the explicit axiom-gap comparison. This project was developed with AI assistance using OpenAI Codex, and relies on the pinned Mathlib library. No claim of mathematical novelty, official acceptance, or guaranteed payment is made.
