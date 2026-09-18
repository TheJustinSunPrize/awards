# JSP-000399: selected set-recovery results in Lean

This is an AI-assisted, self-submitted formalization of selected known results associated with [JSP-000399](../../problems/catalog-0301-0400.md#JSP-000399) and [Erdős problem 494](https://www.erdosproblems.com/494), offered for statement and evidence review. It claims neither a new mathematical discovery nor priority of formalization, and does not complete every variant of the problem. The proposed `submissions/` location is subject to maintainer guidance.

## Exact scope

| Result | Checked declaration | Source |
| --- | --- | --- |
| For every natural number m, two distinct positive-integer sets of size 2^m have identical pair-sum multisets | `SumRecovery.power_two_positive_counterexamples` | [SumRecovery.lean](SumRecovery.lean) |
| Distinct six-element positive-integer sets have identical triple-sum multisets, including every nonnegative translation | `SumRecovery.triple_counterexamples` | [SumRecovery.lean](SumRecovery.lean) |
| For every k ≥ 3, two distinct positive-integer sets of size 2k have identical k-sum multisets | `Recovery.all_k_positive_counterexamples` | [Complement.lean](Complement.lean) |
| Three integer entries are uniquely recovered, up to permutation, from their pair-sum multiset, even with repeated entries | `Recovery.three_element_unique` | [Complement.lean](Complement.lean) |

The size-one pair-sum example (m = 0) is intentionally included: both pair-sum multisets are empty. The non-power-of-two uniqueness classification and general sufficiently-large-cardinality uniqueness results are outside this package.

Duplicate-free lists represent finite sets. `List.Perm` expresses multiset equality, preserving multiplicity. The recursive sum functions enumerate increasing-position subsets; duplicate-free input makes these subsets consist of distinct elements. The Nat and Int developments are self-contained and use only bundled `Std`. There is no machine-checked adapter to mathlib `Finset ℂ`. Although the usual embeddings preserve these counterexamples mathematically, this package does not claim a checked complex-number statement or such an adapter.

## Proof ideas

For pair sums, start with different singleton lists and recursively replace a pair A, B by A ∪ (B+t), B ∪ (A+t), choosing disjoint ranges. The two cross-sum multisets agree, and the within-block sums agree by induction. The source separately proves distinctness, cardinality, lack of duplicates, and positivity.

The six-element triple-sum witnesses are {1,5,6,7,8,9} and {3,4,5,6,7,11}. The finite equality is checked by Lean's `decide`; the translation identity is proved for arbitrary shifts.

For the 2k-element construction, begin with C = {-5,-1,0,1,2,3}, of total sum zero. Append fresh opposite pairs ±(10+j). The resulting set still has total sum zero and differs from its negative because -5 is present and 5 is absent. Complementation pairs each k-subset with another k-subset of opposite sum. Hence C and -C have equal k-sum multisets. A common shift makes both sets positive. `Recovery.complement` proves the general complement identity, and `balanced_invariant` verifies the construction's properties.

For three-entry recovery, the pair sums u, v, w determine the total T = (u+v+w)/2. The original multiset is {T-u,T-v,T-w}. The Lean proof uses integer equalities and permutations rather than finite search.

## Reproduction and evidence

Use Lean **4.24.0**, pinned in [lean-toolchain](lean-toolchain). From this directory:

```sh
./verify.sh
python3 independent_check.py
```

Alternatively set `LEAN_BIN=/absolute/path/to/lean` when running `verify.sh`. The script rejects other Lean versions and checks both files with `lean -t 0`. No external Lean packages are required.

[verification.log](verification.log) records a successful local run and the main declarations' axiom reports. These contain only standard Lean axioms (`propext`, `Quot.sound`, and, for some declarations, `Classical.choice`), without `sorryAx`. The proof sources have no admitted proof or added mathematical axiom.

[independent_check.py](independent_check.py) performs separate finite enumeration for k = 3 through 8 and all 286 three-entry multisets in [-5,5]; its output is [finite-checks.json](finite-checks.json). These checks supplement, and do not replace, the universal Lean proofs. [SHA256SUMS](SHA256SUMS) identifies the files in this directory, excluding the manifest itself.

Local compiler success is not independent verification or maintainer acceptance. The submitter is the account opening the pull request; Codex assisted with proof construction, checks, and preparation. This self-submission is a relevant attribution conflict. No recipient identity, award decision, eligibility change, curator signature, or independent-review status is asserted. The catalog's status fields are unchanged.

## References and licensing

- [Pinned catalog entry at the submission base](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000399).
- [Erdős problem 494](https://www.erdosproblems.com/494), for the problem and known-result context.
- Selfridge and Straus, [On the determination of numbers by their sums of a fixed order](https://doi.org/10.2140/pjm.1958.8.847) (1958), as cited by the catalog.
- Gordon, Fraenkel and Straus, [On the determination of sets by the sets of sums of a certain order](https://doi.org/10.2140/pjm.1962.12.187) (1962), as cited by the catalog.

Code is contributed under the repository's [Apache-2.0 license](../../LICENSE); documentation and data follow [LICENSE-CONTENT](../../LICENSE-CONTENT). The mathematical context is attributed above; no originality or priority claim is made.
