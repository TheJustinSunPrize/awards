# JSP-000404 / Erdős 504: the five-point lower bound

**Partial formalization. This package does not prove the general Sendov classification.**

Every finite set of at least five distinct points in the Euclidean plane contains
three pairwise distinct points forming an angle of at least `3*pi/5` (108 degrees).
The final theorem uses Mathlib's standard `EuclideanSpace ℝ (Fin 2)` and
`EuclideanGeometry.angle`. There is no general-position, convexity, ordering, or
noncollinearity assumption.

## Relationship to the problem and existing work

The original problem is [Erdős 504](https://www.erdosproblems.com/504), catalogued as
JSP-000404. The corrected lower branch of Sendov's classification is
`pi * (1 - 2/(2*n+1))` for `2^n < N <= 2^n + 2^(n-2)`, with `n >= 2`.
At `n=2, N=5` this is `3*pi/5`.

[PR #42](https://github.com/TheJustinSunPrize/awards/pull/42), by superpilot69 and
the credited contributors, already formalizes the corrected construction upper
bounds, including `alpha(5) <= 3*pi/5`. Its fixed head
`722cb3caa86710c788296ca0ec954a79e9a0adcc` explicitly lists the matching five-point
lower bound as unfinished. This package supplies that lower-bound statement.
It does not copy or import PR #42's Lean source. The two packages currently use
different toolchains (this package: Lean 4.19; PR #42: Lean 4.34), so no combined
machine-checked `alpha(5) = 3*pi/5` theorem is claimed here.

The underlying mathematics is historical, not a newly solved conjecture. See
Sendov, *A minimax problem for point configurations*, Acta Mathematica Hungarica
69 (1995), 27–46, [DOI](https://doi.org/10.1007/BF01874605), and the
[Russian exposition](https://www.mathnet.ru/php/getFT.phtml?jrnid=fpm&paperid=81&what=fullt).
The original question is attributed to Erdős and Szekeres. No global first-formalization
claim, catalog eligibility change, or award entitlement is asserted.

## Formal statement and proof

The public entry point is `SendovFivePointPlane.finite_set_large_angle` in
[SendovFivePointPlane.lean](SendovFivePointPlane.lean):

```lean
theorem finite_set_large_angle (s : Finset Point) (hs : 5 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      3*Real.pi/5 ≤ EuclideanGeometry.angle a b c
```

`Point` is an abbreviation for `EuclideanSpace ℝ (Fin 2)`. Finset cardinality
counts distinct points, and the conclusion explicitly excludes repeated vertices.
The angle is at `b`, measured in radians. The theorem also applies when some
points are collinear.

The proof has three layers:

1. [SendovFiveDirections.lean](SendovFiveDirections.lean) proves an inequality for
   the ten joining-line directions of five ordered points. Each of the ten
   triangles gives one of two closed orderings and linear angular constraints.
   A finite tree of 179 splits and 180 leaves proves `5/2 <= t` using Lean's
   `linarith` at every leaf.
2. [SendovDirectionGeometry.lean](SendovDirectionGeometry.lean) proves these
   constraints from genuine complex-plane angles. If all angles are at most
   `pi-lambda`, normalize directions by `(arg+pi/2)/lambda`, with `t=pi/lambda`.
   Triangle angle sums prove the required direction ordering. Multiplication
   by a nonzero complex number gives distinct real coordinates, which can be
   sorted without changing angles. Consequently `lambda <= 2*pi/5`.
   Choosing the largest angle among finitely many distinct triples gives an
   angle at least `3*pi/5`.
3. [SendovFivePointPlane.lean](SendovFivePointPlane.lean) transfers the result
   through Mathlib's complex/Euclidean-plane linear isometry and selects five
   points from an arbitrary larger finite set.

The optional [generator](generate_five_direction_proof.py) used Z3 5.1.0 to prune
the finite proof tree and choose sufficient linear hypotheses. **Z3 is not a
trusted oracle and is not needed to verify the submitted Lean files.** All leaves
are checked by Lean. Different Z3 versions may generate a different valid tree.

## Reproduce and inspect the evidence

Use the pinned [lean-toolchain](lean-toolchain), [lakefile](lakefile.toml), and
[dependency manifest](lake-manifest.json). With Lean 4.19.0 and Python 3 available:

```sh
lake exe cache get
python verify.py
```

The script checks all pinned dependency Git revisions and rejects tracked changes,
builds the three modules, then runs `lean --trust=0` on each submitted source file.
Nine printed declaration audits cover the final theorems and key bridge results;
each audited theorem's transitive axiom set must be contained in
`propext`, `Classical.choice`, and `Quot.sound`.

The [verification record](verification/result.json) binds source hashes, dependency
revisions, exit codes and log hashes. Local checks reuse compiled Mathlib caches;
they do not rebuild Mathlib from source in an isolated environment. `--trust=0`
is a same-implementation recheck. A separate [Nanoda check](INDEPENDENT.md)
has now checked the final theorem and 18,045 declarations in its dependency
closure, using only the same three standard axioms. Deliberately invalid proof
and axiom controls are rejected. This uses an independent implementation, run
by the submitter. Official statement-fidelity review, isolated verification,
independent reviewer sign-off, attribution review and any award assessment remain outstanding.

## Scope still missing

The matching general lower bounds for arbitrary `N` in both Sendov branches are
not proved. This package neither establishes a general reduction to three
clusters nor assumes such a reduction as an axiom. It supplies the five-point
case only, with the immediate consequence for sets of at least five points.

The submission was prepared by GitHub user zilan520 with Codex assistance. Mathlib
and the historical mathematical sources retain their original attribution.
Code and documentation follow the repository's respective licenses.
