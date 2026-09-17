# Proof of the optimal minimum-denominator asymptotic

Let X_k consist of finite sets A of k distinct positive integers with
sum(1/a, a in A) = 1. For k ≥ 3, let B(k) be the greatest minimum of a set in X_k.
The submitted theorem is

```text
lim(k → infinity) B(k)/k = 1/(e - 1).
```

This is the minimum-denominator question in JSP-000242. No bound on the largest
denominator is part of X_k. The argument below is classical mathematics; its
Lean implementation and the correspondence of its statements are the proposed
contribution. It does not establish Croot's stronger short-interval theorem.

## 1. The actual extremum and padding

The fixed-cardinality search is proved equivalent to existence of a finite set,
without a cutoff on its largest denominator. Every feasible minimum is at most
k. The finite search over minima therefore produces an attained greatest value.
Starting with {2,3,6}, replace the largest a by a+1 and a(a+1). These two new
denominators are distinct and larger than every other denominator, and
1/a = 1/(a+1) + 1/(a(a+1)). This gives feasibility at every k ≥ 3 and
monotonicity of B(k).

Formal declarations: `possible_iff_finset`, `optimalMinimum_isGreatest`,
`extend_representation`, `optimalMinimum_mono`.

## 2. A short expansion for an arbitrary small rational

First, repetitions can be removed without increasing length when the reciprocal
sum is at most one. For a repeated even denominator a, replace its two copies
by a/2. For repeated odd a ≥ 3, put b=(a+1)/2 and use

```text
2/a = 1/b + 1/(ab).
```

The even replacement shortens the list. The odd replacement keeps its length
and reduces the first changed entry, placing b at the earlier repeated entry
and ab at the later one. Thus the list decreases in the well-founded shortlex
order. The sum bound excludes repeated a=1, and positivity is preserved. This
proves termination without a bound on the denominators. It is a direct
implementation of the classical duplicate-removal principle associated with
Takenouchi; it is not asserted as a new mathematical result.

For a<n!, expand a/n! in at most n positive unit fractions by induction.
Writing a=nq+r with 0≤r<n gives

```text
a/n! = q/(n-1)! + r/n!.
```

The first term is handled by induction. If r>0, then r divides n!, so the
second is the single unit fraction 1/(n!/r). Internal repetitions are harmless
at this step because they will be removed.

Now let 0≤a<b≤n!, and write a*n!=b*s+r, with 0≤r<b. Both s and r are less
than n!, so

```text
a/b = s/n! + (1/b)(r/n!)
```

has a positive unit-fraction expansion with at most 2n terms. Remove all
repetitions as above. This proves the classical factorial remainder bound.
The denominator b need not be reduced. The method is attributed to Erdős's
1950 paper, whose Theorem 1 bounds expansion length in terms of the denominator:
[original article](https://www.renyi.hu/~p_erdos/1950-02.pdf).

Formal declarations: `remove_repetitions`, `factorial_expansion`,
`egyptian_length_factorial`.

## 3. Finish a harmonic prefix

Write H(k,m)=sum(1/d, m≤d<m+k). Suppose m≥1, H(k,m)≥1, and
L=lcm(1,...,m+k)≤n!. Starting with remainder 1, subtract consecutive
reciprocals whenever the next reciprocal does not exceed the remainder.
The envelope condition guarantees that, after at most k subtractions, the
remainder r is nonnegative and smaller than the next reciprocal 1/d, or zero.
At every step the reduced denominator of r divides L.

Use the factorial bound to expand r in at most 2n distinct terms. Any term
1/x in this positive expansion satisfies 1/x≤r<1/d, so x>d. Consequently
the tail is disjoint from the prefix and all denominators are at least m.
We obtain a representation of 1 with at most k+2n terms.

Formal declarations: `small_target_short`, `short_representation_of_envelope`,
`representation_card_le_of_lcm`.

## 4. The tail costs a vanishing proportion of the terms

Pinned Mathlib proves Chebyshev's estimate

```text
log(lcm(1,...,N)) ≤ (log 4 + 4) N.
```

For any fixed integer D, this is linear in t when N=Dt, while log(t!) grows
faster than any fixed multiple of t. The implementation uses an elementary
finite bound: choose A≥exp(2C), where C=(log 4+4)D. For t≥2A,

```text
t! ≥ A^(t-A),
log(t!) ≥ (t-A) log A ≥ Ct.
```

Therefore lcm(1,...,Dt)≤t! eventually. This is proved, not assumed.

Fix positive integers q and p with (e-1)q<p. The integral lower estimate gives

```text
H(pt,qt) ≥ log((p+q)/q) > 1.
```

Apply the preceding construction with m=qt, k=pt, n=t and D=p+q. For all
sufficiently large t there is a representation with minimum at least qt and
at most (p+2)t terms. Padding makes the length exactly (p+2)t. Hence

```text
B((p+2)t) ≥ qt.
```

For every sufficiently large k, take t=floor(k/(p+2)) and use monotonicity:

```text
B(k)/k > q/(p+2) - q/k.
```

Taking p=floor((e-1)q)+1 and arbitrarily large q gives the lower limit
1/(e-1), for all large k, not merely a subsequence.

Formal declarations: `log_le_envelope`, `lcm_dilation_le_factorial`,
`optimalMinimum_blocks`, `optimalMinimum_lower_from_blocks`,
`optimalMinimum_eventual_lower`.

## 5. Matching upper bound and conclusion

Distinct denominators with minimum m have reciprocal sum at most H(k,m).
The strict midpoint-integral estimate proved in the analytic module implies

```text
B(k) < k/(e-1) + 1/2.
```

Together with the quantified eventual lower bound, this proves
`optimalMinimum_tendsto`. The formal theorem has no unproved analytic or
number-theoretic hypothesis. Its audited axiom closure consists only of
`propext`, `Classical.choice`, and `Quot.sound`.

The number-theoretic construction can produce very large final denominators.
No conclusion about an optimal maximum, a shortest interval, or the open
second-order question in JSP-000251 follows from the submitted limit theorem.
