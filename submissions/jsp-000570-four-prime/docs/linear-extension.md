# Version 3: a linear separation criterion

For natural P,a,b,c, assume a>=1, b>=3a, c>=3b+1, P>=100c^5, and
P,P+a,P+b,P+c all prime. The theorem `four_prime_exact_linear` proves

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b).

The statement still covers every 2<=k<=floor(N/2). No pair-exclusion, digit,
or prime-existence hypothesis has been added. The parameter c only needs to
grow linearly with b under this new sufficient condition.

## Preservation and strict extension

Version 1 assumed c>=10b^2; version 2 assumed c>=b(b-a)+b+1.
Since b>=3a and a>=1 imply b-a>=2, the version-2 bound implies c>=3b+1.
Both published theorem names and types remain available as proved corollaries.

For a=2,b=6, the respective c thresholds are 360, 31, and now 19.
The choice c=20, P=320001821 yields the four primes
320001821,320001823,320001827,320001841 and satisfies P>=320000000=100*20^5.
It satisfies the new assumptions and violates both old c thresholds.
The [supporting numerical check](../verification/witness.json) uses exact trial
division to the integer square root; run `python tools/check_witness.py` to
reproduce it. This separate computation is not a Lean primality proof, an
enumeration of f(N), or an infinitude claim.

## Why the proof changes

The original last-pair argument used d=c-b>L=b(b-a). That condition is removed.
For zero carry H=0, the raw low and middle coefficients are K=d(ud-t) and M=t-2ud.
If K<0, then -K<=dL=C<F, contradicting the allowed low digit after its borrow.
If K>=0 and u>0, then t<=ud, and M<0 contradicts the middle digit bound.
If K>=0 and u=0, all source digits vanish, contradicting the positive index.

The positive-carry argument continues to use L<c^2. The raw congruence and
low-coefficient bounds are re-proved separately using ud^2+dL<q and
ud^2+d^2<q. Thus no old L<d premise remains hidden in a normalization lemma.
Every target bound is connected to actual integer division and remainder.

The false old auxiliary inequality d>L is removed. Its replacement is
L<c^2. Together with the other 32 inequalities, it has a new positive-polynomial
certificate under a=1+x, b=3a+y, c=3b+1+z for nonnegative x,y,z.
Lean checks the identities and signs; the optional Python generator is not
part of the trusted proof.

## Scope

This strengthens the local four-prime criterion. It does not raise the 3/4
exponent, establish an optimal separation threshold, or solve the full problem.
Maynard, infinitude, and the asymptotic limit remain outside this formalization.
Global novelty, external peer review, official verification, contribution
attribution, and any award remain matters for subsequent review.
