# Independent source and statement review

Reviewed on 2026-09-17 by a separate Codex agent from the authors of the FCC proof modules. This is an AI source-level mathematical and specification review, not an independently implemented second kernel, a human peer review, or a claim of mathematical novelty. The reviewer did not modify any proof source.

All eight modules under `FCC/`, the root import module, the README, proof exposition, and the audit declaration list were read. The hashes below bind the review to the final local proof sources.

| File | SHA-256 |
| --- | --- |
| `FCC.lean` | `1442d53ff73a5ed93b1915045599e01c37917933d167b095a2111423ab776b03` |
| `FCC/Basic.lean` | `28a7fcd815292a31d5151e9d4e82d0005a62f3c0f4899febfb259e60a791d880` |
| `FCC/Bounds.lean` | `f51f4283a25e505b2eea8e5a0097c05030d11f99bbcb4e5cc4df608dee6e2b12` |
| `FCC/ContactGraph.lean` | `811ddcd9d77e3e4cffa9213b7a88558cd384372a4eafbab0c68561c031521910` |
| `FCC/CountCore.lean` | `8d3ee2d26ab8667f1856cc0934829044008bdd6cc4c0f1a9e323af7b1e4a343a` |
| `FCC/Counting.lean` | `9db137622db71e3debd81b5bc68b7b6b3bc952632209a21f4dbb6e0a0f303ec4` |
| `FCC/Geometry.lean` | `b64a5c734b3ca43446eedcab33d52cf1f2205360248d24e94890ace9ce91ebde` |
| `FCC/Padding.lean` | `413e3e2ae2fbe7c13f5c1cf92b2b2c7735f74317510939a4c77a157b09076d97` |
| `FCC/Scale.lean` | `7ad1e1737843afe87ea02a77a1a4535e2314bcb60f74ea2b24e17751803f8b9a` |

## Actual Euclidean geometry and cardinality

`Vertex m` is the finite index type `Fin 4 × (Fin m × Fin m × Fin m)`. The four offsets are exactly 000, 011, 101, and 110. `coord` adds these offsets to twice the cell coordinates, and `point` divides the resulting real coordinates by `sqrt 2` in the actual type `EuclideanSpace ℝ (Fin 3)`, with its Euclidean metric.

The proof does not assume an abstract contact relation has a geometric realization. `coord_injective` recovers the label and cell coordinates; `point_injective` certifies that different index vertices represent different real points. Together with `vertex_card`, this gives exactly `4*m^3` distinct points.

The sum of the integer coordinate differences is even, so their squared-distance sum is even. Positivity for distinct vertices comes from coordinate injectivity, giving integer squared distance at least two. `point_dist_sq` proves that the real squared distance is this integer sum divided by two. `point_separated` and `point_dist_eq_one_iff` then prove actual distance at least one and equivalence of the integer contact criterion with actual distance exactly one.

## Exact contact count and absence of duplicate edges

The six class-pair lemmas handle every pair of distinct offset labels. For a representative pair, squared distance two is equivalent to one equal cell coordinate and two coordinates that are equal or consecutive. `even_odd_odd_square_iff` proves this characterization over integers, rather than assuming that only nearest candidate pairs need inspection.

`stepEquiv` is a bijection from equal-or-consecutive coordinate pairs to `Fin (2*m-1)`. The flipped relation is counted by swapping endpoints. `product_relation_count` uses an explicit equivalence of finite types to multiply the three independent coordinate counts. Each of the six class pairs contributes exactly `m*(2*m-1)^2`.

There are no contacts within one offset class: the squared integer distance would be divisible by four and cannot equal two. Thus ordering the two distinct class labels omits no contact. `contactPairs_card_sum` accounts for all six class pairs and yields `6*m*(2*m-1)^2`.

Crucially, `contactGraph` is a Mathlib `SimpleGraph` whose adjacency is defined directly as Euclidean distance one. Its `edgeFinset` contains `Sym2` unordered pairs. `contactGraph_edgeFinset_eq` proves equality with the image of the canonically oriented counting pairs. `contactPairs_sym2_injOn` excludes the swapped-endpoint ambiguity using the strict order of the class labels. Consequently the exact result counts each genuine unordered geometric contact once, with neither a missing class nor an unproved factor-of-two conversion.

## Padding and the all-cardinalities theorem

The added points are explicitly `(2*m+2+2*i,0,0)`. The first coordinate of every FCC point is at most `2*m`, and distinct added points are at least two apart. A proved coordinate-gap estimate bounds the full Euclidean distance below by two. The padded point map is injective and all distinct padded points have distance at least one.

`paddedPoint_contact_iff` proves that a distance-one pair has both endpoints in the original FCC part. `paddedContactGraph_eq_map` therefore identifies the actual padded unit-distance graph with the original graph embedded by `Sum.inl`. The final source also proves `paddedContactGraph_edgeFinset_eq` directly: every padded unit-distance edge is exactly an unordered image of an original canonical contact. The reverse direction handles both endpoint orders using `Sym2.eq_iff`. Its edge-count proof applies `card_image_of_injOn`, extracts endpoint equality with `Sum.inl.inj`, and again rules out the reversed orientation by the strict class order. Therefore the count is unchanged, with a checked direct bridge to the actual padded graph rather than just a selected pair counter.

For every natural `n >= 4`, `exists_box_scale` finds an integer `m >= 1` satisfying `4*m^3 <= n < 4*(m+1)^3`. It uses the first cube scale above n and proves the required predecessor bounds. Taking `q=n-4*m^3` gives an index type of cardinality exactly n; the lower inequality prevents truncated subtraction from changing that cardinality.

The final `all_cardinalities` theorem includes the cardinality, geometric injection, separation of every distinct pair, and the lower bound on the actual unordered Euclidean graph edges. Hence it supplies an n-point configuration for every n in its stated range, not just the cubic subsequence.

## The exponent and explicit constant 200

The exponent is explicitly `(2/3 : ℝ)`, so it is real division and does not truncate to zero. From `4*m^3 <= n`, the proof obtains `m^2 <= n^(2/3)` using nonnegative real powers.

For `m >= 1`, the exact contact count expands to `24*m^3-24*m^2+6*m`. The proof justifies the natural-to-real cast of `2*m-1` using `1 <= 2*m`. The upper bound on n gives

`6n - E_m < 96m^2 + 66m + 24 <= 186m^2 <= 200m^2 <= 200n^(2/3)`.

This confirms the conservative constant used by `contact_count_lower_bound`. No optimality of 200 is asserted, and the potentially negative lower bound for small n is valid. The formal proof uses polynomial inequalities to establish the same estimate.

## Empty and small boundary cases

At `m=0`, the cell and vertex types are empty, so both the number of points and the number of contacts are zero. The `stepEquiv` target `Fin (2*m-1)` is also empty because subtraction is natural and truncated. The geometry statements quantify over an empty domain; they do not produce nonexistent points.

At `m=1`, the four offsets give four distinct points, all six offset-class pairs contribute one contact, and the count is six. The arithmetic expansion and the all-size theorem only use a positive m, as required. The theorem `all_cardinalities` has the explicit hypothesis `4 <= n`; no claim for smaller n is smuggled through the scale-selection argument. Padding is valid for arbitrary q, including q=0.

## Finding and limits

No statement mismatch, missing geometric realization, duplicate unordered-edge counting, hidden cubic-subsequence restriction, or boundary error was found in the reviewed source. The declarations prove the classical exact FCC construction, its isolated-point padding, and the stated lower bound for every n >= 4.

The result does not establish a universal upper bound, the optimal contact number, the Bezdek--Reid theorem, or the full two-sided conclusion of Erdős problem 1084. Source review and Lean verification do not establish global formalization priority or award eligibility. The machine-verification results and their dependency trust boundary are recorded separately.
