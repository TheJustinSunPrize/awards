# JSP-000118: counterexamples for every k ≥ 4

[Erdős #106](https://www.erdosproblems.com/106), catalogued as [JSP-000118](../../problems/catalog-0101-0200.md#JSP-000118), asks whether `f(k²+1)=k`, where `f(n)` is the supremum of sums of side lengths of `n` squares packed in the unit square, with no common interior points. The already published 17-square example disproves the universal equality at `k=4`. This package independently verifies an exact rational seed and extends it to **every natural k ≥ 4**, with a complete geometric statement:

```lean
theorem geometric_counterexamples (k : ℕ) (hk : 4 ≤ k) :
    ∃ P : List Square, P.length=k^2+1 ∧ (k : ℝ)<total P ∧
      (∀ S ∈ P, 0<S.side ∧ S.u^2+S.v^2=1 ∧ S.carrier ⊆ box 1) ∧
      P.Pairwise (fun S T => Disjoint S.interior T.interior)
```

Each square has center `(x,y)`, unit side direction `(u,v)`, and positive side length `s`. Its points are `(x+αu−βv, y+αv+βu)`, with `|α|,|β|≤s/2` for its closed carrier and strict inequalities for its interior. `box 1` is the closed unit square. Pairwise disjoint interiors of positive squares also exclude repeated squares in the list, so its length counts distinct genuine squares. Rotations and boundary contact are permitted. `jsp_000118` directly refutes the proposed universal upper bound on these geometric packings; a packing with sum greater than `k` cannot coexist with the claimed supremum `f(k²+1)=k`.

This is a full disproof and a parameterized strengthening. It does not determine `f(n)` for arbitrary `n`, prove optimality of the exhibited packings, or resolve small parameters `k=1,2,3`.

## Complete construction

In a container `[0,4]²`, take the 17-square rational configuration encoded explicitly by `seed` in [Main.lean](Main.lean). Its constants are

```text
a = 851228/1048735,   C = 1073566/1048735,
b = 2−a,             D = 2−C,
E = 2a+C−2,          h = E/(49/41).
```

Eight unit squares fill the first two columns. Three squares of side `a` start at `(2,0)`, `(2,a)`, `(2,2a)`; two of side `b` start at `(2+a,0)`, `(2+a,b)`. The last three axis-parallel squares have lower-left corners and sides `(2,4−C,C)`, `(2+C,4−D,D)`, and `(4−E,2b,E)`. The tilted square has center `(4−3E/2,2b+E/2)`, direction `(40/41,9/41)`, and side `h`. The direction is unit because `40²+9²=41²`.

The total side length in this container is

```text
8 + 3a + 2b + C + D + E + h = 16 + 78/1048735 > 16.
```

Containment is checked using projection radii. For a direction `w`, the projection radius of a square is

```text
R(S,w) = s/2 · (|w₁u+w₂v| + |−w₁v+w₂u|).
```

The x and y radius bounds place the entire closed carrier inside its container. For each of the 136 unordered square pairs, the proof checks a separating direction from `(1,0)`, `(0,1)`, `(40/41,9/41)`, and `(-9/41,40/41)`, and verifies that the center projection separation is at least the sum of radii. `projection_strict` proves that interior projections are strictly inside these intervals; `separated_disjoint` therefore turns the arithmetic certificate into actual geometric disjointness, including touching pairs. All checks use exact rational constants in real arithmetic and kernel-checked normalization.

For the inductive step from a container `[0,k]²` to `[0,k+1]²`, retain the old packing and add the `k+1` unit squares with lower-left corners `(i,k)` for `0≤i≤k` and the `k` unit squares at `(k,j)` for `0≤j<k`. These form the new top row and right column. They fit the larger container, their interiors are mutually disjoint, and x/y separation bounds keep them disjoint from the old packing. The count becomes

```text
(k²+1) + (2k+1) = (k+1)²+1,
```

and the side sum increases by `2k+1`, preserving strict excess over the container side squared. Induction from four covers all `k≥4`. Scaling every center and side by `1/k` places the resulting packing in the unit square, preserves directions and disjointness, and makes its side sum greater than `k`. The same construction has exact side sum `k+78/(1048735k)`; the exported theorem certifies the strict inequality needed for the disproof, rather than asserting optimality.

## Attribution and incremental scope

The [catalog-linked pinned Lean source](https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos106.lean) supplies the seed's mathematical data and credits **A. Raj Singh** for its informal proof and **Codex / GPT-5.6 Sol** for its formal proof. That source proves the counterexample at `k=4`. The catalog currently credits **Conner Silverstein** for its selected 17-square result; the linked source's specific seed credit differs. This submission follows the seed source's explicit attribution and leaves the catalog unchanged. Related existing recipient recommendation: [#203](https://github.com/TheJustinSunPrize/awards/issues/203).

Neither the seed nor the first mathematical or Lean disproof is claimed as new. The requested review concerns the parameterized extension for every `k≥4`, its scale and perimeter-padding proofs, and this independently developed, compact geometric implementation. The extension is not stated in the inspected pinned source; that observation is not a global priority claim. The mathematical idea of padding is elementary, and no new mathematical discovery is asserted. This package imports only pinned Mathlib and does not copy or import the earlier Lean proof. The rational configuration is mathematical data, reproduced with attribution.

Prepared with OpenAI Codex assistance. Any formalization-recipient identity remains `RECIPIENT-JSP000118-ALLK-A`, confirmation pending. No catalog, candidate, eligibility flag, award or payment record changes. Organizer review determines contribution scope and eligibility; no award is announced.

## Reproduction and verification

Lean is pinned to `v4.34.0`, Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`; transitive dependencies are locked in [lake-manifest.json](lake-manifest.json). With the pinned Lean toolchain installed, from this directory run:

```sh
lake exe cache get Mathlib.Basic.Real.Basic Mathlib.Data.Fin.VecNotation Mathlib.Data.List.FinRange Mathlib.Algebra.BigOperators.Group.List.Basic Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.Positivity
lake build
lake env leanchecker --verbose Main
```

The cache command accelerates the build; `lake build` is the normal proof-checking command. The exact-module replay uses Lean's own kernel against its imported pinned environment. Imported cache artifacts remain trusted; a full dependency rebuild or an independently implemented checker is not claimed.

Local checks on macOS arm64, 2026-09-17: build, direct elaboration and exact-module kernel replay passed. Axiom reports for `all_sizes`, `unit_counterexamples`, `geometric_counterexamples` and `jsp_000118` contain only `propext`, `Classical.choice`, `Quot.sound`. There are no proof holes, custom axiom declarations or compiler-based decision proofs.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `Main.lean` | 15128 | `03e9f2059bf023dffbbfd814708c3b5ac0520bde0b20e1bbe34d5d0977bf99ec` |
| `lake-manifest.json` | 3546 | `5a45bc0eed02adc43431844675851b13f4e1b6179285fcc91fa4b9d84598aee1` |

Permanent archival evidence and byte comparisons are recorded in the PR once available. Designated independent verification remains pending; repository CI checks structure and does not establish mathematical review or an award.
