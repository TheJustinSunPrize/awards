# Proof of the finite FCC construction

The formalization uses real three-dimensional Euclidean space with its usual `L²` metric. All contact counts refer to unordered pairs of distinct points at distance exactly one.

## Coordinates and number of points

Let

\[
D=\{(0,0,0),(0,1,1),(1,0,1),(1,1,0)\}.
\]

For each `a` in the four-element set `D` and each cell `c=(c₁,c₂,c₃)` with `0 ≤ cᵢ < m`, set

\[
z(a,c)=2c+a,\qquad p(a,c)=\frac{z(a,c)}{\sqrt 2}.
\]

This parameterization is injective: the coordinate parities recover `a`, and then dividing the coordinate differences by two recovers `c`. There are exactly `4m³` indices and hence exactly `4m³` points. Every coordinate of `z` lies between zero and `2m-1`, and the sum of its coordinates is even.

Lean declarations: `FCC.offset`, `FCC.coord`, `FCC.point`, `FCC.vertex_card`, `FCC.coord_injective`, and `FCC.point_injective`.

## Separation and the contact criterion

For two integer coordinate vectors `z,z'`, let

\[
S=\sum_{i=1}^3(z_i-z_i')^2.
\]

The sum of coordinate differences is even. Since an integer and its square have the same parity, `S` is even. If the indices are distinct, injectivity gives `S>0`, so `S≥2`.

The actual Euclidean distance satisfies

\[
\|p-p'\|^2=S/2.
\]

It follows that distinct points have distance at least one, and that their distance is exactly one if and only if `S=2`. This last condition is the decidable integer relation `FCC.Contact` used for counting.

If two indices belong to the same parity class, every coordinate difference is even and `S` is divisible by four. Such a pair cannot satisfy `S=2`. Thus every contact joins different classes.

Lean declarations: `FCC.sqDist_even`, `FCC.sqDist_pos_of_ne`, `FCC.sqDist_ge_two`, `FCC.point_dist_sq`, `FCC.point_separated`, `FCC.point_dist_eq_one_iff`, and `FCC.Contact.offset_ne`.

## Exact boundary-sensitive contact count

Consider the classes `(0,0,0)` and `(0,1,1)`. For cell indices `c,d`, the unscaled coordinate differences have the form

\[
(2(c_1-d_1),\;2(c_2-d_2)-1,\;2(c_3-d_3)-1).
\]

The squared distance is two precisely when

\[
c_1=d_1,\qquad c_2-d_2\in\{0,1\},\qquad c_3-d_3\in\{0,1\}.
\]

The first coordinate gives `m` choices. Each of the other coordinates gives `m+(m-1)=2m-1` choices when `m≥1`: `m` equal pairs and `m-1` consecutive pairs. The empty case is covered by natural truncated subtraction. Consequently this class pair contributes exactly `m(2m-1)²` contacts.

The other five unordered pairs of classes have the same count. Coordinate roles may change, and a consecutive-pair relation may be reversed; neither change affects its cardinality. The formal proof establishes the six cases separately and factors the three independent coordinate choices through an explicit equivalence of finite types.

There are six unordered pairs of the four classes, so

\[
E_m=6m(2m-1)^2.
\]

Lean declarations: `FCC.stepEquiv`, `FCC.step_count`, `FCC.step_flip_count`, `FCC.eq_pair_count`, `FCC.product_relation_count`, `FCC.classPairCount_01` through `FCC.classPairCount_23`, and `FCC.contactPairs_card`.

## Why this counts genuine unordered Euclidean contacts

The integer counting set `contactPairs m` selects contacts whose first class label is less than the second class label. A contact always has different labels, so exactly one orientation is selected.

Independently, `contactGraph m` is defined as a `SimpleGraph` on the index type with adjacency given directly by `dist (point u) (point v) = 1`. Its edge finset consists of `Sym2` unordered pairs. The formalization proves that this edge finset is the image of `contactPairs m`, and that the orientation map is injective on those pairs. The graph therefore has exactly `E_m` edges. The injectivity of the point map ensures that these index vertices represent distinct geometric points.

Lean declarations: `FCC.contactGraph`, `FCC.contactGraph_edgeFinset_eq`, `FCC.contactPairs_sym2_injOn`, and `FCC.contactGraph_edge_card`.

## Padding to an arbitrary larger cardinality

For `i=0,...,q-1`, add

\[
r_i=(2m+2+2i,0,0).
\]

Every original FCC point has first coordinate at most `2m`. Therefore its first-coordinate gap from every `r_i` is at least two, which bounds the full Euclidean distance below by two. Distinct added points also have distance at least two.

The combined point map on `Vertex m ⊕ Fin q` is injective and separated by at least one. No contact involves an added point, so the combined graph has exactly the original `E_m` contacts. Its actual point image has cardinality `4m³+q`.

Lean declarations: `FCC.point_first_le`, `FCC.point_far_dist`, `FCC.farPoint_dist`, `FCC.paddedPoint_separated`, `FCC.paddedPoint_injective`, `FCC.paddedPoint_contact_iff`, `FCC.paddedPoints_card`, `FCC.paddedPoints_separated`, `FCC.paddedContactGraph_eq_map`, `FCC.paddedContactGraph_edgeFinset_eq`, and `FCC.paddedContactGraph_edge_card`. The padded edge-finset equality is proved directly using `Sym2`, and its cardinality proof again rules out a reversed duplicate using the strictly ordered class labels.

## Relation to the all-size lower bound

For every `n ≥ 4`, choose `m ≥ 1` with

\[
4m^3\le n<4(m+1)^3.
\]

The formal proof takes the smallest integer `k` for which `n<4k³` and puts
`m=k-1`. The assumption `n≥4` forces `k≥2`, so `m≥1`; minimality gives the lower
inequality. Put `q=n-4m³`. The padding construction then has exactly `n` points.

Its number of contacts is

\[
E_m=24m^3-24m^2+6m.
\]

Using the upper bound on `n`, its deficit satisfies

\[
\begin{aligned}
6n-E_m
&<96m^2+66m+24\\
&\le186m^2\\
&\le200m^2\\
&\le200n^{2/3}.
\end{aligned}
\]

Here `m≥1` gives `m≤m²` and `1≤m²`, and `m³≤n` gives `m²≤n^(2/3)` by
monotonicity of nonnegative real powers. The coefficient `200` is a convenient
explicit choice; no optimality is claimed.

`FCC.all_cardinalities` combines these facts. It supplies natural numbers `m,q`,
proves that `Vertex m ⊕ Fin q` has cardinality `n`, proves injectivity and pairwise
separation of its Euclidean point map, and bounds the actual graph's unordered
edge count below by `6*n-200*n^(2/3)`.

Lean declarations: `FCC.exists_box_scale`, `FCC.scale_square_le_rpow`,
`FCC.contact_count_lower_bound`, `FCC.exact_contacts`,
`FCC.exact_padded_contacts`, and `FCC.all_cardinalities`.

The exponent is real exponentiation by `(2/3 : ℝ)`, not natural division. The
final theorem has the stated threshold `n≥4`; it does not define an extremal
supremum `f₃` or assert a universal upper bound on contact numbers.

## Recorded verification

The strict full-package build, the 20-declaration axiom audit, and the
same-kernel replay of the root and all eight local submodules each exited zero.
The audit reported no axioms outside `propext`, `Classical.choice`, and
`Quot.sound`. A separate Codex agent reviewed the statement and mathematical
meaning of the nine proof modules; its source hashes and findings are in
`statement-review.md`. The trusted dependency-cache and same-kernel limits are
recorded in `verification/result.json` and the README.
