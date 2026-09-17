# Version 4: the offset-dependent separation boundary

Historical version-4 note. Its theorem is retained as a corollary of the
[version-5 criterion](cubic-size.md). The size bound and example
below describe the unchanged preceding release.

For natural P,a,b,c, assume a>=1, b>=3a, c>=3b-a+1, P>=100c^5,
and P,P+a,P+b,P+c all prime. The theorem `four_prime_exact_boundary`
proves

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b),
    f(N) = min_{2<=k<=floor(N/2)} gcd(N,binom(N,k)).

Only the hypothesis on c changes. The theorem still supplies all six pair
exclusions and covers the full minimum range. No auxiliary digit hypothesis
is added to the root declaration. In the Lean natural-number statement the
subtraction is untruncated because a<=3b follows from a>=1 and b>=3a.

## What changes in the proof

Write R=a+c-3b. The high digit of N/(P+b) is R-1. The new condition gives
R>=1, allowing R-1=0 in the general integer lemmas. The P+b source bound
0<=u<=R-1 then forces u=0 at R=1. The existing zero-source and carry branches
cover this case; no missing positive-index case is discarded.

The uniform lower bound for c is now 9. The 33 polynomial certificates are
regenerated using a=1+x, b=3a+y, c=3b-a+1+z for x,y,z>=0. There are
32 strictly positive certificates and one nonnegative certificate R-1=z.
The generator records and checks the inequality sign. Lean verifies every
identity and sign independently of the Python generator.

The previous manuscript's justification B>b(c-3b)>0 cannot be used in this
range. For B=(2b-a)c+2ab-3b^2, the corrected identity is

    B = 3b(b-a)+a^2+(2b-a)(c-3b+a) > 0.

Here b>=3a, a>=1, and c-3b+a>=1. The remaining row normalizations,
Euclidean digit bounds, and large-base estimates use the unchanged P bound.

## Strict extension and a prime example

Version 3 assumed c>=3b+1, version 2 assumed c>=b(b-a)+b+1, and
version 1 assumed c>=10b^2. All three declaration names and original types
remain as proved corollaries of the new theorem.

For a=2,b=6, the successive c thresholds are 360,31,19,17. Taking c=18
and P=189078581 gives the four primes

    189078581, 189078583, 189078587, 189078599.

This satisfies P>=188956800=100*18^5 and the new separation condition,
while violating all three preceding c conditions. The standard-library
script `python tools/check_witness.py` in the version-4 archive verifies primality by full trial
division through each integer square root; see [that archive](../verification/archive-v4.md).
This calculation is separate from Lean and does not enumerate f(N).

Since the root's large P makes all four primes odd, the offsets a,b,c must
be even. Thus c=3b-a+1 itself is not a prime-tuple boundary case: its right
side is odd. The integer digit lemmas nevertheless prove that exact boundary,
and the example above is the nearest even c for a=2,b=6.

## Scope

This strengthens a local sufficient criterion. It does not establish an
optimal separation threshold, raise the 3/4 exponent, or solve the full
Erdős problem. Maynard, infinitude, and the asymptotic limit remain outside
the Lean formalization. The archives are self-published evidence; global
novelty, external peer review, official verification, and any award remain
unestablished by these local checks.
