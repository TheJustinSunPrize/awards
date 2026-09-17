# Statement and scope

Let `s >= 2`, and prescribe positive integers `u_0,...,u_(s-1)` in their given
order. No distinctness or monotonicity of this seed is assumed. Set `a_i=u_i`
for `i<s`. For `n>=s`, let `a_n` be the least integer strictly greater than
`a_(n-1)` expressible as

\[
\sum_{i=p}^{q-1} a_i,\qquad 0\le p,\quad p+1<q\le n.
\]

The indices are consecutive; the values of the summands need not be consecutive
integers. The condition `p+1<q` requires at least two terms. All summands precede
the new term. This is the usual rule, shifted from one-based to zero-based indexing.

The package proves:

1. Such an infinite sequence exists and is unique (`exists_unique_extension`).
2. For every natural `M`, there is `N` such that `M+n <= a_n` for all `n>=N`
   (`arbitrary_seed_result` and `constructed_sequence_result`). This expresses
   divergence of the signed excess `a_n-n`, not merely unbounded values of `a_n`.
3. The set of positive integers not in the full range of `a`, including its
   seed, is infinite (the second conjunct of those theorems).
4. On the increasing tail, `a_i+j <= a_j+i` for `i<=j`
   (`excess_monotone`), the subtraction-free form of monotonicity of the signed excess.

`seed : Nat -> Nat` is just a convenient encoding of the finite list: the
predicate and conclusions constrain only its first `s` entries. Uniqueness
ensures that entries beyond the finite seed cannot affect the extension.
`IsGreedyExtension` includes all seed equalities, the strict inequality, a valid
block representation, and minimality among all admissible values.

The stronger general theorem `excess_tends_to_infinity` assumes only positivity,
strict increase after a finite index, and a representation by an earlier block
for every sufficiently late term. The exact greedy rule is proved to satisfy
these assumptions, rather than taken as an unverified bridge.

The underlying arbitrary-seed qualitative result is stated by Tang in
[version 1, Theorem 1.4](https://arxiv.org/html/2603.09939v1), and discussed in
[version 2, Section 6.1](https://arxiv.org/html/2603.09939v2#S6.SS1).
This package does not establish `a_n=n+o(n)`, a new quantitative lower bound,
or the polynomial upper bounds for the classical sequence.
