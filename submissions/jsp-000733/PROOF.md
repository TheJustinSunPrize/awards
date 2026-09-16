# Leading asymptotic for primitive subset sums

Let f(n) be the largest cardinality of A contained in {1,...,n} such that
no two distinct positive values among its nonempty subset sums divide one
another. The proved target is f(n)/log_2(n) -> 1 as n -> infinity.

## Finite upper bound

All subset sums of an admissible A are distinct, including the empty sum.
Indeed, cancel the intersection of two equal-sum subsets. If the remaining
disjoint subsets S,T are nonempty, their common sum s is positive. Both s
and the sum 2s of their union are nonempty subset sums. The divisibility
s | 2s contradicts primitivity because s and 2s are distinct. Positivity
also excludes an empty subset having the same sum as a nonempty subset.

Consequently the 2^k subsets of A, where k=|A|, inject into the integer
interval [0,nk]. Hence 2^k <= nk+1. The same inequality holds for f(n)
because the finite maximum is attained.

## Existing lower bound and assembly

The construction {2^m-2^i : 0<=i<m} of Erdős, Lev, Rauzy, Sándor and
Sárközy supplies f(n)>log_2(n)-1. Its existing Lean proof is imported
from the hash-checked, downloaded plby/lean-proofs dependency, pinned at
8822f7ddef30fadbd92e1c6ab4ed897af356af5e. This is prior formal work.

Write k=f(n). The lower bound implies k -> infinity. For n>=1 the upper
bound gives 2^k <= n(k+1), and taking natural logarithms yields

    log(2) - log(k+1)/k <= log(n)/k.

The lower construction gives the opposite estimate

    log(n)/k <= log(2) + log(2)/k.

Both errors tend to zero. Squeezing, inversion and the change-of-base
identity give k/log_2(n) -> 1. The Lean assembly discharges the finite
upper and lower hypotheses against the actual extremal function.

## Contribution and scope

New work consists of the primitivity-to-injectivity bridge, the finite
counting upper bound against the same definitions, and the unconditional
leading asymptotic assembly. The mathematical observation and counting
argument are established mathematics, not a new mathematical discovery.
Existing counting results conditional on distinct subset sums are also
present in rjwalters/lean-genius; they are acknowledged in the source.

This target does not give the exact value of f(n), nor a constant-error
refinement, nor the sharper published half-log-log upper error. A July
2026 unreviewed mathematical refinement claim is recorded separately in
the novelty review; no claim is made that this submission settles it.

## Sources

- https://www.erdosproblems.com/882
- https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean
- https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos882ProblemOQ03.lean
