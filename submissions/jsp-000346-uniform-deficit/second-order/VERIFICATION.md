# Verification record

Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. All nine dependency checkouts matched the manifest and had clean tracked sources. Compiled caches were used, including the real-topology dependencies for the density bridge; not all dependencies were rebuilt from source.

The main module contains 337 lines and 17 named theorems. The source builds without warnings. Every named theorem's axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`. There are no unfinished proof declarations, problem-specific axioms, `native_decide`, or unsafe proof escapes.

Fresh replay with `lake env leanchecker --fresh --verbose SecondOrder` passed in **75.004 seconds**. This uses Lean's official kernel and is not an independently implemented checker or organizer-designated review.

Supplementary exact checks:

- All 65,536 subsets of `{2,...,17}` were tested for full consecutive-block product uniqueness by exact integer multiplication; 36,600 passed.
- On those sets, and on an independently generated 135-term greedy finite prefix, 658,951 finite witness checks verified the disjoint families and the finite inequality.
- All 1,001 Lean cube-root outputs for `N=0,...,1000` agreed with an independent binary-search implementation.
- The adjacency-only greedy construction at `N=1,000,000` has `E(N)=972` and `E(100)=8`; it violates the new finite inequality (`1100>1045`). This checks that the earlier, weaker adjacency hypothesis is insufficient.
- The positive integers from 2 onward provide a second negative control: density one alone does not imply the new inequality.
- Small integer-root arithmetic examples use `decide +kernel`.

Finite-set tests inspect the finite combinatorial argument and do not establish an infinite extension or the asymptotic theorem. The Python checks are not formal proofs. The density-one asymptotic conclusion rests on the universally quantified Lean argument and its standard real-limit bridge.

The exact Lean conclusion is the all-integer-parameter inequality stated in README. Replacing integer roots by real roots and expressing it as a normalized liminf is an elementary interpretation explained in PROOF.md; no separate Lean theorem using real cube roots or `Filter.liminf` is claimed.

`verification/verification.json` records commands, elapsed times and hashes of proof inputs and logs. The public `SHA256SUMS` manifest covers the package except itself. Repository policy checks are recorded separately and do not certify mathematical significance or prize eligibility.
