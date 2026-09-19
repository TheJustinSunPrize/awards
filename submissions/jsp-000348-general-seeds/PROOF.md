# Proof guide

The argument below is the one implemented in `GeneralSeeds.lean`. It avoids
using an unformalized Diophantine finiteness theorem.

## An eventually consecutive tail is impossible

Suppose that, from index `n0` onwards, `a_n=T+(n-n0)` for a positive integer `T`.
Let `S` be the sum of all terms before that index. Choose

\[
k=2S+T^2+T+2,\quad X=2^{k+1},\quad P=2^{2k+1}.
\]

Then `2P=X^2`, `P>S`, `P>=T`, and both `T^2<X` and `2S+T<X`.
The consecutive tail contains `P`, which must have an earlier block representation.

If this block ends before the tail, its sum is at most `S`, a contradiction.
If it lies entirely in the tail, it expresses a power of two as a sum of at
least two consecutive positive integers. This is impossible: twice such a
sum factors as `d(2x+d-1)`, with one odd factor greater than one, whereas every
odd divisor of a power of two is one (`power_two_obstruction`).

In the remaining case the block crosses the start of the tail. Its initial
part has sum `C` with `0<=C<=S`, and its final term has value `v`. Summing the
arithmetic progression gives

\[
v(v+1)+2C+T=X^2+T^2.
\]

If `v<X`, then `v(v+1)<=(X-1)X`, so the left side is strictly less than `X^2`.
If `v>=X`, then `v(v+1)>=X(X+1)`, so the left side is strictly greater than
`X^2+T^2`. Both contradict the displayed identity. This proves
`no_consecutive_tail`. The finite sums are handled by `twice_interval`.

## Divergence and omissions

Shift to an increasing tail, writing `g(t)=a_(s+t)`. The natural-valued function
`b(t)=g(t)-t` is nondecreasing. If bounded, its range is finite and attains a
maximum. Monotonicity makes it constant after a finite index, creating exactly
the consecutive tail just ruled out. Hence `b` is unbounded, and monotonicity
upgrades this to divergence (`excess_tends_to_infinity`). Reversing the index
shift gives the stated quantifiers `forall M, exists N, forall n>=N, M+n<=a_n`.

If only finitely many positive integers were omitted, choose `K` above all of
them. For `n` on the increasing tail, every integer from `K+1` through `a_n`
would appear among indices `0,...,n`: any later term is larger than `a_n`.
There are at most `n+1` such values, so `a_n-K<=n+1`, contradicting divergence.
This also counts seed entries and allows their duplication.

## The greedy sequence exists uniquely

For every `n>=s>=2`, the sum of the first `n` entries exceeds the last entry,
because the first entry is positive and has a different index from the last.
It is therefore an admissible candidate. The least candidate exists in the
natural numbers. Finite approximations update one new index at a time; their
stability produces an infinite sequence satisfying the exact rule.

Strong induction gives uniqueness: agreement at all earlier indices gives
the same predecessor and the same candidate block sums, whose minima coincide.
`greedy_is_extension` proves existence, `extension_unique` proves uniqueness,
and `arbitrary_seed_result` supplies the bridge to the general divergence theorem.

The arbitrary-seed conclusion is known from Tang; this is a formal proof of
that scoped result. The earlier classical-seed formalization is credited in
[PRIOR_ART.md](PRIOR_ART.md), including its elementary alternative argument.
