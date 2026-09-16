# Automated source-scope review

Review date: September 16, 2026. This review concerns definitions, theorem
scope, and correspondence with the mathematical source. A Codex task agent
reviewed the sources and also implemented the balanced counting module;
therefore this is not an independent human review of every component.
The completed compilation and independent-checker results, together with
the exact checked source snapshot, are recorded in the
[expanded-package verification receipt](verification/finite-v2/VERIFICATION.md).
New run evidence is stored under `verification/finite-v2/`; the earlier records
under `verification/` are retained.

## Original problem and retained results

`Erdos882.nonemptySubsetSums A` takes the finite image of sums of nonempty
subsets of `A`; repeated numerical values are identified. `IsPrimitive`
requires that divisibility between two such values force equality.
`Admissible n A` also requires `A ⊆ Finset.Icc 1 n`.

`maximumSize n` is `Finset.max'` of the finite, nonempty family of attainable
admissible cardinalities. Its attainment theorem supplies an actual admissible
set of that size. This remains the same original extremal quantity throughout
the extension. The original seven production source files are unchanged. The
original definitions were independently implemented and do
not import the separate lower-construction formalization.

The retained theorems are `korsky_sum_bound` and `original_upper_bound`. Their
modular packing includes the constant-2 word and its zero residue. The new
finite packing is a separate use of the existing ordered-word collision lemma.

## New balanced family and exact count

`Word k` is `Fin k → Fin 3`. `Ordered w` forbids an earlier 2 followed by a
later 0. `Balanced w` means `Ordered w` together with coordinate sum `k`.
Thus the numbers of zeros and twos agree. The all-ones word is balanced,
including at size zero; no requirement that a 2 occur is added.

For positive `k`, `balanced_card` proves the cardinality `2^(k-1)`. Each even
Boolean support determines exactly one balanced word: selected coordinates
are first zeros and then twos in equal numbers; other coordinates are ones.
A recursive encoder proves reconstruction and the inverse support identity.
The parity condition determines the first Boolean bit from the remaining
`k-1` bits. This is a proof for arbitrary positive `k`, not enumeration of a
fixed collection of sizes. At `k=1` the balanced family has one member.

## Interval bounds and collision hypothesis

For monotone natural weights, `balanced_value_lower` proves
`total a ≤ value a w` for balanced words, with the comparison in the integers.
If the word contains a 2, the proof selects its first occurrence; otherwise
balance forces the all-ones word. Selecting an arbitrary later 2 would not
justify the pointwise sign argument.

`balanced_value_upper` assumes strictly increasing weights, all at most `n`.
The reverse-rank gap `a i + (k-1-i.val) ≤ n` and the bounded coordinates imply

```text
value a w + floor((k-1)^2/4) ≤ k*n.
```

The rank inequality itself needs only the coordinate sum, not `Ordered`.
Strict monotonicity is stronger than mere monotonicity and is supplied by the
sorted enumeration of a finite set in the original-problem bridge.

`NoDouble a` quantifies over all nonempty pairs of index subsets, including
intersecting subsets, and prohibits a ratio of 2. Positive weights are explicit
final hypotheses. Original primitivity implies this condition: if positive
subset-sum values satisfy `x = 2*y`, then `y` divides `x`; primitivity forces
`x=y`, contradicting positivity. Distinct subsets need not have distinct sums
as an additional assumption.

The core is nonvacuous. A single positive weight satisfies `NoDouble`; weights
1 and 3 give a further example, with nonempty subset-sum values `{1,3,4}`.
The latter illustrates that `NoDouble` is weaker than primitivity.

## Closed-interval packing and finite endpoint

The existing `ordered_value_injective` applies to balanced words without a
`Good` hypothesis. Their distinct values lie in the closed integer interval

```text
[total a, k*n - floor((k-1)^2/4)].
```

The subtraction here is in the integers. The all-ones word proves the
interval nonempty before its cardinality is used. The closed interval supplies
the final `+1`, giving

```text
total a + 2^(k-1) + floor((k-1)^2/4) ≤ k*n+1.
```

Combining this with the retained sum bound gives
`(k+1)*2^(k-1) + floor((k-1)^2/4) ≤ k*n+1`.
For positive `k`, this is the ceiling-free form of Korsky's (1.8).
At `k=1`, it reduces to `2 ≤ n+1`, equivalently `1 ≤ n`.
At `k=2` and `k=3`, it implies respectively `n ≥ 3` and `n ≥ 6`.
No nonempty-generator theorem is applied at `k=0`.

The sorted enumeration is an order embedding `Fin A.card ↪o ℕ`; it preserves
membership, cardinality, and indexed subset sums. This discharges positivity,
strict monotonicity, the upper bound by `n`, and `NoDouble` for an actual
admissible set.

`original_threshold_bound` obtains an attained extremal set. If its size
exceeds `m`, it chooses a subset with exactly `m+1` elements, proves that the
subset is still admissible, and applies the finite bound at that size. The
strict threshold contradicts that bound. No monotonicity of a threshold
function is assumed. The statement covers all natural `n,m`; empty sets and
`m=0` do not introduce a positive-cardinality assumption about the maximum.

The final four new exports are:

1. `korsky_deficit_bound` — the interval deficit inequality.
2. `korsky_finite_bound` — its combination with the retained sum inequality.
3. `original_finite_bound` — the same finite inequality for every nonempty original admissible set.
4. `original_threshold_bound` — an upper bound on the attained original maximum under the explicit strict threshold.

All intermediate count, interval, collision, and bridge requirements are
supplied in `Erdos882KorskyFinite.lean`. No unproved form of the desired bound
is exposed as a final theorem hypothesis.

## Literature correspondence and scope limits

The retained sum inequality is Theorem 1.1 (1.6) and Proposition 2.2 (2.6).
The new deficit estimate is (1.7), also Proposition 3.2 (3.3). The finite
estimate is the multiplied, ceiling-free form of (1.8). The threshold theorem
captures the upper-bound argument used in Corollary 1.3. The formalization uses
direct interval packing instead of defining the paper's intermediate `R`.

The separate ELRSS lower construction is neither imported nor reproved. Hence
this package does not establish the equality conclusion of Corollary 1.3 or
the two-value statement of Corollary 1.2. “Lower” in one module name refers
only to the lower endpoint of a weighted-word interval.

PR #31 covers the leading asymptotic. PR #264 at reviewed head
`1db509ec5ad2c410d9b13232685c343c008f0b1f` covers the half-log-log bound with
original-problem and maximum-attainment bridges. The comparison is limited to
those inspected snapshots and is not a global priority claim.

The accompanying `ExtensionNegativeControls.lean` states explicit guards for
the order, monotonicity, strict-monotonicity, floor, and closed-interval
endpoint requirements. Their actual run results, source identities, theorem
axioms, and independent-checker evidence must be supplied by the final receipt;
this source audit does not substitute for those results. Permanent external
archive status is also **PENDING**, with no receipt inferred from a local file.
