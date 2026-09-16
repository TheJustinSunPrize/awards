# Automated source-scope review

Review date: September 16, 2026. This review examines mathematical scope and
definitions. It is not an official verifier's attestation or an independent
kernel-checker result. An additional Codex task agent conducted the review;
that agent also implemented the counting module, so the review is not
independent of every proof component. Final run evidence must identify the
exact reviewed and checked source snapshot.

## Original mathematical statement

`Erdos882.nonemptySubsetSums A` takes sums over `A.powerset.erase ∅` and forms a
finite image, identifying repeated numerical values. The excluded subset is
exactly the empty set. `IsPrimitive B` states that divisibility between two
values in B forces equality. `Admissible n A` combines this condition with
`A ⊆ Finset.Icc 1 n`.

`attainableSizes n` is the finite image of cardinalities of all admissible
subsets of the interval. The empty set makes this family nonempty.
`maximumSize n` is its `Finset.max'`, and `maximumSize_attained` supplies an
actual admissible set of that size. The target is therefore the original
extremal maximum, not a constant chosen to satisfy the desired bound.

The definitions and finite-maximum implementation are newly written for this
package. They do not import the published lower-construction implementation.

## Core hypothesis and nonvacuity

`NoDouble a` quantifies over all pairs of nonempty index subsets, including
intersecting subsets, and forbids one subset sum being twice another. Positive
weights are explicit hypotheses of the sum bound. The hypothesis is weaker
than primitivity: weights 1 and 3 have subset-sum values {1,3,4}, with no
ratio-two pair, although 1 divides 3. The sum bound is an equality in this
example, so its hypotheses are meaningful and nonvacuous.

`Word k` is `Fin k → Fin 3`. `Ordered` forbids an earlier 2 followed by a later
0; `Good` additionally requires at least one 2. The constant-2 word is retained
for every positive k. The count is proved for every positive k by a first-entry
bijection and induction, not by finite enumeration.

## Packing and boundary cases

For a good word, the weighted integer value satisfies `0 < value ≤ 2*total`.
Coefficient cancellation under `NoDouble` proves equal values imply equal
ordered words and excludes a difference equal to the positive total. Equal
residues therefore can differ only by 0 or one positive/negative total, and the
collision lemmas give injectivity into `ZMod total`.

The constant-2 word has value `2*total` and residue zero. It is included in the
injection; residue zero is not discarded. For k=1 the good family consists of
one word, and the conclusion is `1 ≤ a₀`, valid for every positive weight.
The packing theorem explicitly assumes k>0. The original-problem theorem
also handles the empty admissible set and n=0.

## Bridge and final hypotheses

The endpoint bridge enumerates an actual finite set by `Fin A.card`. An index
subset maps to a subset of A with the same sum. If two nonempty subset sums
satisfy `x=2*y`, positivity gives y>0 and y divides x. Primitivity then forces
x=y, contradicting positivity. Thus no extra subset-sum-injectivity condition
is silently assumed.

The total is at most `A.card*n`. The packing inequality and positive cardinality
give `2^(A.card-1) ≤ n`, from which the integer-logarithm bound follows. The
attainment lemma transfers it to the actual maximum. A zero-cardinality set is
handled separately.

The final statements under review are only:

1. `Erdos882Korsky.korsky_sum_bound`: for positive k and positive natural
   weights under `NoDouble`, `k*2^(k-1) ≤ total a`.
2. `Erdos882Korsky.original_upper_bound`: for every natural n,
   `Erdos882.maximumSize n ≤ Nat.log 2 n + 1`.

The final assembly supplies all intermediate collision and packing hypotheses.
No unproved version of the main theorem remains as a final theorem parameter.
Actual compilation, axiom dependencies, negative controls, and independent
checker outcomes must be read from the verification receipt; this source
review does not certify those runs.

## Exact literature and prior-work correspondence

Korsky's sum bound is Proposition 2.2, equation (2.6), and equation (1.6) within
Theorem 1.1. The extremal upper consequence is equation (3.6), used in the proof
of Corollary 1.2. This package does not claim all of Theorem 1.1 or a formalized
Corollary 1.2: the submitted endpoint is the upper inequality alone.

PR #31 covers the leading asymptotic. PR #264 at reviewed head
`1db509ec5ad2c410d9b13232685c343c008f0b1f` covers the full half-log-log bound for
n at least 32, with genuine original-condition and maximum-attainment bridges.
Its seven Lean modules do not contain this constant additive-error endpoint.
The distinction is mathematical scope; this review does not dismiss its
result on account of differences in checker configuration.

Permitted after successful verification: a complete Lean formalization of
Korsky's sum inequality and the original extremal constant-error upper bound.
Excluded claims: a new mathematical discovery, an exact extremal formula,
a submitted lower bound or two-value theorem, all strengthened finite results
in the manuscript, worldwide priority, official acceptance, or guaranteed
prize payment.
