# Statement correspondence

## Original secondary question

The remarks to [Erdős Problem 795](https://www.erdosproblems.com/795) attribute to
Erdős a proposed exact expression for the extremal size of a set with distinct
subset products. This is different from the main asymptotic upper bound, which
has an affirmative answer.

Write `F(k)` for the maximum size of an additively dissociated subset of
`{1,...,k}` and `pi(x)` for the number of primes at most `x`. The secondary formula
is `sum pi(N^(1/k))`, taking precisely those `k` where `F(k) > F(k-1)`.
Raghavan's paper, Section 1, describes the same expression using the inverse
threshold function (the smallest possible largest element of a dissociated
set of each prescribed cardinality).

## Formal definitions

- `subsetProducts xs` enumerates one product for every positional subset. Its
  length is proved to be `2 ^ xs.length`. Empty subsets have product one.
- `Admissible N xs` requires `xs.Nodup`, every member to lie in `[1,N]`, and
  `subsetProducts xs` to have no duplicate. Thus the list represents a finite
  set of cardinality `xs.length`. The arbitrary-characteristic-function theorem
  explicitly bridges the certificate to ordinary subsets.
- `subsets` is the standard recursive powerset enumeration: exclude the head,
  or include it in each subset of the tail.
- `subsetSums` enumerates all subset sums, with empty sum zero. `F` exhausts
  all subsets of `[1,k]`, filters those with distinct sums, and maximizes size.
- `isPrime p` requires `p >= 2` and excludes every divisor from 2 through `p-1`.
- `primeRootCount N k` counts such primes with `p^k <= N`. This equals
  `pi(N^(1/k))` for positive `k`, with no floating-point rounding.
- `predicted N` sums the terms up to `Nat.log2 N`. Every further term is zero
  because any prime is at least 2.
- `IsExtremalValue N m` states both an upper bound for every admissible set
  and the existence of an admissible set of size `m`. It is a maximum, not
  merely a proposed lower bound.
- `ExactFormulaConjecture` asserts this maximum equals `predicted N` for all `N`.

At 48, the kernel computes `F(0..5) = [0,1,2,2,3,3]`; only exponents 1, 2 and 4
contribute. Their prime counts are 15, 3 and 1. The 20-element witness therefore
contradicts the upper-bound conjunct of the exact conjecture. No claim is made
that `g(48) = 20`; the proved bound `g(48) >= 20` suffices.

## Proof structure

The eight-element core `{5,25,6,16,27,32,36,48}` has 256 distinct subset products,
checked by `decide`. The other twelve members are distinct primes coprime to
the entire product of the core and the previously inserted primes. The proved
lemma `extend_coprime` adds them one at a time. If the new factor is present
on only one side of an equality, it would divide the old total product, contrary
to coprimality. If it is present on both sides, cancellation reduces the equality
to the old set. This verifies all 2^20 products without a large computation
being admitted as an axiom.

## Deliberately limited conclusions

This file does not prove Raghavan's asymptotic theorem, improve its asymptotic
error, establish the smallest counterexample, or claim first mathematical
disproof of the exact formula. Eligibility for a separate award requires the
organizer's assessment of this scope and the prior formalization record.
