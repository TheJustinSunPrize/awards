# Formal statement correspondence

The original JSP-000346 / Erdős 421 problem asks for a positive, strictly increasing sequence of natural density one whose products over all distinct nonempty consecutive blocks are different. This package proves a necessary omission bound for every such sequence, and more generally for every strictly increasing sequence with the block-product property, regardless of density.

## Definitions

- `DistinctBlockProducts a`: for all natural u, v, u', v' with u <= v and u' <= v', equality of the two products over `Finset.Icc` implies both endpoints agree.
- `AvoidsAdjacentProducts B`: for any x < y in B with no B-member strictly between them, x*y is not in B. Adjacency is in the ordered set B; it does not mean y=x+1.
- `deficit B N`: the cardinality of `{x in Finset.Icc 1 N | x not in B}`. Zero is never counted.
- `Nat.sqrt`: the integer square root. Iterating it means `floor(sqrt(floor(sqrt N)))`.

The sequence is indexed starting at zero. The original indexing starting at one is obtained by shifting indices; the property quantifies over every nonempty index interval. `distinct_blocks_iff_injOn` checks equivalence with the pair-of-endpoints injectivity formulation in the [fixed formal-conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean).

## Theorem inventory

| Lean theorem | Exact role |
| --- | --- |
| `finite_bound` | Arbitrary B and all N,m,t: m*m <= N and m < (t+1)*(t+1) imply m <= deficit B N + t + 1, under adjacency-product avoidance. |
| `sqrt_bound` | Substitute the two integer square roots. |
| `avoids_of_distinct_blocks` | Original block-product condition plus strict increase implies adjacency-product avoidance on the range. |
| `sequence_sqrt_bound` | Uniform finite bound for the original sequence property. |
| `distinct_blocks_iff_injOn` | Equivalence of the two block-product predicates. |
| `original_statement_bound` | The same finite bound directly from the original pair-of-endpoints `Set.InjOn` hypothesis. |
| `coefficient_one_bound` | For all k>=1, N>=(2k)^4: (k-1)*sqrt(N) <= k*deficit B N. |
| `sequence_coefficient_one_bound` | The all-parameter coefficient-one statement for the sequence property. |

[Audit.lean](Audit.lean) prints the actual elaborated types and axiom closures. The machine output is in [verification/axioms.log](verification/axioms.log).

## Exclusions

The proved statements do not assert the existence of any density-one sequence, an O(sqrt(N)) omission construction, optimality, a solution of every part of the original research question, or priority over all unpublished or unindexed work. No analytic-number-theory result is assumed as an extra axiom. The elementary real-valued asymptotic interpretation is explained in PROOF.md; the machine-checked asymptotic formulation is the quantified integer inequality above.
