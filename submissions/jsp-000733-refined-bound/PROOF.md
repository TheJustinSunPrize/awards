# Proof

Let `A ⊆ {1,…,n}` have a primitive numerical set of nonempty subset sums. If distinct subsets have equal sums, remove their intersection. The remaining disjoint subsets have a common positive sum `s`, while their union has sum `2s`, contradicting primitivity. Thus the subset-sum map is injective, including on the empty subset.

Put `k=|A|` and define the integer `z_S=2Σ_{a∈S}a−Σ_{a∈A}a` for each subset. Finite-set induction, pairing `(z−a)²+(z+a)²`, gives

\[
\sum_{S\subseteq A}z_S^2=2^k\sum_{a\in A}a^2.
\]

If `k≥2`, set `t=2^(k−2)`. There are `4t` distinct values `z_S`. The integer half-open interval `[-t,t)` contains only `2t` integers, so at least `2t` squared values are at least `t²`. Therefore `2t³≤4tΣa²`. Cancel the positive factor `2t` and use `Σa²≤kn²` to obtain `4^k≤32kn²`. This nonoptimal constant preserves the required coefficient of the log-log term.

Now suppose `n≥32` and put `L=log₂n≥5`. For `k≥2`, taking logarithms gives

\[
2k\le5+\log_2 k+2L.
\]

The interval containment gives `k≤n`. Hence `2k≤5+3L≤4L`, so `k≤2L`. Substitute `log₂k≤1+log₂L` into the first inequality to obtain `k≤L+(1/2)log₂L+3`. The cases `k=0,1` follow from a lower bound on the right side. All these steps are implemented in `LogBound.lean`; the finite bound is proved rather than retained as a hypothesis of the final theorem.

Every admissible set belongs to `(Icc 1 n).powerset`. Filtering by admissibility produces a finite nonempty family, since the empty set is admissible. Define `maximumSize` as the `Finset.sup` of cardinalities and prove that an admissible set attains it. Applying the bound to this set yields the result for the actual `f(n)`. The threshold 32 then gives the eventual statement in `Filter.atTop`.

For the classical mathematical background, see Moser's second-moment method in the first proof of [Dubroff–Fox–Xu, arXiv:2006.12988v2](https://arxiv.org/html/2006.12988v2). The constant 32 is the coarse counting choice in this implementation, not the optimal constant in that paper.
