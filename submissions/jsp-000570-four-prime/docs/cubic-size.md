# Version 5: a cubic base-size requirement

Historical version-5 extension note. The positive theorem remains unchanged
in version 6, which additionally [formalizes the counterexample](counterexample-formal.md).

For natural P,a,b,c, assume a>=1, b>=3a, c>=3b-a+1, P>=12c^3,
and P,P+a,P+b,P+c all prime. The theorem `four_prime_exact_cubic` proves

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b),
    f(N) = min_{2<=k<=floor(N/2)} gcd(N,binom(N,k)).

Only the lower bound on P changes from version 4. All four previously
published theorem names and types remain as corollaries. No pair-exclusion,
digit, or prime-existence hypothesis is added to the root declaration.

## Why a cubic bound suffices

The actual common size margins used by the proof are

    11c^3 < P, 13c^2 < P, 7c^3 < P, and 10c <= P.

The first three supply the pair normalizations and the final carry argument.
The last gives N<=(P+c)^4<2P^4, so every k<=N/2 has k/x<x^3 for each
base x>=P. Since the gap assumptions give c>=9, all four margins follow
from P>=12c^3. The shared helper uses c>=2; each caller proves that bound
from the unchanged gap assumptions. No new root hypothesis is introduced.

The 33 parameter-polynomial certificates remain 32 strict inequalities and
one nonnegative inequality R-1>=0, where R=a+c-3b. All six missing-prime
pair exclusions and the full index range are preserved. The generic pair,
Lucas, and minimum cores require no change.

For an old root satisfying P>=100c^5, the inequalities c>=1 and
12c^3<=100c^3<=100c^5 yield the new bound, preserving the previous results.
The coefficient 12 is sufficient; it is not claimed to be optimal.

## A strictly new prime example

Take a=2,b=6,c=18,P=75011. The four primes are

    75011, 75013, 75017, 75029.

Here 69984=12*18^3<=75011<188956800=100*18^5. Thus the example satisfies
the new theorem and violates version 4's P requirement. The new size
threshold is 2700 times smaller for c=18. The script
`python tools/check_witness.py` verifies primality by full exact trial
division; see [the record](../verification/witness.json). This supporting
calculation is separate from Lean and does not enumerate f(N).

## Why simply deleting the gap condition's final +1 fails

The candidate c>=3b-a, with every other version-4 premise unchanged, is
false. Let a=6,b=18,c=48 and P=25480409371. All four integers

    P, P+6, P+18, P+48

are prime, and P>=25480396800=100*48^5. Set their product to N and
k=19P^2(P+18). One has 2<=k<=N/2. With q=P+18, the low-first quotient
digit tables are

| Base | Digits of N/base | Digits of k/base |
| --- | --- | --- |
| P | [5184,1260,72,1] | [0,342,19,0] |
| q | [6480,q-684,q-1,0] | [6156,q-684,18,0] |

Lucas therefore shows that P and P+18 do not divide binom(N,k). At the
other two prime bases, N has units digit zero while k does not:
k is congruent to 8208 modulo P+6 and to -1313280 modulo P+48.
Those two primes do divide the binomial coefficient. Since N is the product
of four distinct primes, this proves

    gcd(N,binom(N,k)) = (P+6)(P+48) < P(P+6)(P+18).

In particular f(N) is strictly smaller than the proposed value. This does
not determine the exact minimum f(N). The full fixed-instance certificate
uses exact trial division and Lucas digit comparisons in
`python tools/check_counterexample.py`; see [its record](../verification/counterexample.json).
It never constructs the enormous binomial coefficient. In the original
version-5 archive, this counterexample was supporting evidence outside Lean.
Version 6 adds a separate Lean proof of all these counterexample facts.
It does not contradict versions 1-5, all of which
exclude that gap boundary, nor establish an optimal more general criterion.

## Scope

The version-5 Lean result is the local cubic-size four-prime equality and
its four preceding corollaries. Version 6 additionally formalizes the
counterexample, without changing those five positive statements. It does not raise the 3/4 exponent or solve
the full problem. Maynard, infinitude, and the asymptotic limit remain outside
the formalization. Global novelty, external peer review, official verification,
and any award are not established by this self-published evidence.
