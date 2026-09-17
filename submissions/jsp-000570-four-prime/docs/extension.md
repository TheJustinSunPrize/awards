# Version 2: weaker separation in the four-prime criterion

Historical version-2 note. Its theorem is retained as a corollary of the
current [version-3 linear criterion](linear-extension.md). The earlier numerical
example is retained here for context; current verification uses a smaller-gap witness.

## Exact change

For natural P,a,b,c, the new theorem assumes

    a >= 1, b >= 3a, c >= b(b-a)+b+1, P >= 100c^5,
    P, P+a, P+b, P+c all prime.

It proves the same exact binomial-gcd minimum:

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b).

The declaration is `Erdos700.FourPrime.four_prime_exact_relaxed`.
For natural subtraction, b>=3a ensures a<=b, and the Lean proof explicitly
uses that order when casting b-a to the integers.

## Why the old result follows

The original bound was c>=10b^2. Under b>=3a>=3,

    b(b-a)+b+1 <= b^2+b+1 <= 10b^2.

Thus every old admissible parameter tuple satisfies the new assumption.
The original `four_prime_exact` name and type are retained as a corollary.
For example, a=2,b=6 previously required c>=360, whereas the new threshold
is c>=31. An even offset c=32 therefore lies in the newly admitted range.
The choice P=3355448021 gives the four primes
3355448021, 3355448023, 3355448027, and 3355448053; P>=3355443200=100*32^5.
The separate numerical check in the [version-2 archive](../verification/archive-v2.md) verifies primality
by exact trial division through the integer square root. Use the version-2 archive's `tools/check_witness.py` to reproduce that earlier example. This is supporting
evidence, not a substitute for the universal Lean proof or a Lean primality proof.

## Proof changes

The decisive largest-prime pair uses c-b>b(b-a), precisely the new integer
condition. The other five pair exclusions and digit-normalization arguments
still work. The supporting 33 strict polynomial inequalities were regenerated
using a=1+x, b=3a+y, c=b(b-a)+b+1+z for nonnegative integers x,y,z.
Each expansion has nonnegative coefficients and a positive constant;
Lean checks every identity and sign. In particular the uniform lower bound
on c drops from 90 to 10, which suffices for all large-base estimates.

The six pair exclusions, the entire 2<=k<=floor(N/2) range, and the minimum
witness k=P+c remain covered. No additional prime-existence, pair-exclusion,
or normalized-digit assumption is added to the root theorem.

## Scope

This expands the local theorem's parameter range. The existing 3/4-exponent
consequence using Maynard remains unchanged and outside this Lean formalization.
It does not solve the full problem, improve that exponent, establish global
priority, or determine an award. Internal AI-assisted reviews remain distinct
from external peer review and designated organizer verification.
