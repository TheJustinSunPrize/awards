# Version 6: a Lean proof of the gap-boundary counterexample

The positive criterion and its four compatibility corollaries are unchanged:
for a>=1, b>=3a, c>=3b-a+1, P>=12c^3, and four displayed primes,

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b),
    f(N) = min_{2<=k<=floor(N/2)} gcd(N,binom(N,k)).

Version 6 additionally proves in Lean that replacing c>=3b-a+1 by
c>=3b-a is false, even if the stronger old size bound P>=100c^5 is kept.
It uses the same definition of f, imported from `Minimum.lean`.

## Concrete statement

In `Erdos700.Counterexample`, define

    P = 25480409371,
    N = P(P+6)(P+18)(P+48),
    k = 19P^2(P+18).

The following declarations have no unproved primality or digit hypotheses:

- `four_primes`: P, P+6, P+18, and P+48 are prime.
- `index_in_range`: 1<k and k<=N/2.
- `gcd_at_index`: gcd(N,binom(N,k))=(P+6)(P+48).
- `f_strict_upper_bound`: f(N)<P(P+6)(P+18).
- `zero_gap_counterexample`: bundles these facts with the actual a=6,b=18,c=48
  parameter and old size inequalities.
- `zero_gap_extension_false`: refutes the universal candidate with
  a>=1, b>=3a, c>=3b-a, P>=100c^5, and the four primality hypotheses.

In particular, this is a formal counterexample to the proposed extension,
not merely a failure of one proof method. The proof supplies an upper bound
on f(N) from one legal index; it does not claim to compute the exact minimum.

## Primalities and finite Lucas support

`CounterexamplePrimes.lean` applies Mathlib's Lucas primality criterion to
the four fixed integers. Complete factorizations of one less than each target
reduce the criterion to smaller prime facts and modular-power identities.
`norm_num` and the proof-producing `reduce_mod_char` tactic discharge those
arithmetic certificates inside Lean. External search results and Python
primality flags are not imported as assumptions.

`CounterexampleLucas.lean` proves a finite converse to Lucas digit support:
if n,k<p^d and each of their first d base-p digits is ordered correctly,
then p does not divide binom(n,k). A generic factorial argument establishes
nondivisibility for a single legal digit pair; Mathlib's Lucas congruence
then peels the columns by induction. It does not evaluate a huge factorial
or binomial coefficient.

For the actual witness, let q=P+18. Its low-first quotient digit tables are

| Base | Digits of N/base | Digits of k/base |
| --- | --- | --- |
| P | [5184,1260,72,1] | [0,342,19,0] |
| q | [6480,q-684,q-1,0] | [6156,q-684,18,0] |

Both full N and k have units digit zero in these two bases. Lean verifies
the required finite comparisons and power bounds, establishing that P and
P+18 are absent from the binomial. At P+6 and P+48, the units digit of N
is zero while that of k is nonzero, so the forward Lucas lemma proves
divisibility. Coprimality and a gcd product identity give the exact gcd.

The final minimum bound uses `Nat.sInf_le` with the explicit in-range index
k and this gcd value. Natural-number arithmetic then proves the strict
comparison with P(P+6)(P+18). The positive four-prime theorem is not used
to prove the counterexample; both proofs share only the verified arithmetic
framework and the definition of f.

## Verification and provenance

The [audit](../verification/canonical-audit.log) prints P,N,k, the exact
function, all five retained criterion statements, all six new counterexample
statements, and their transitive axiom lists. The [build record](../verification/build-record.json)
and [source hashes](../verification/source-files.json) identify the freshly
rebuilt source snapshot. The project contains no `sorry`, custom mathematical
axiom, or `native_decide` bypass in these proofs.

The original exact Python calculation remains available as a supplementary
[check](../tools/check_counterexample.py) with a [record](../verification/counterexample.json).
The original [v5 archive](../verification/archive-v5.md) preserves the version
in which the counterexample was still outside Lean. The new formal proof is
checked independently of running that Python program.

## Limits

This formalizes a boundary obstruction and strengthens the verification of
the submitted partial result. It does not change the 3/4 exponent, prove an
optimal more general parameter condition, or solve all of Erdős 700. Maynard,
prime-family infinitude, and the asymptotic limit remain outside the Lean
development. Internal AI-assisted review is not external peer review or
official prize verification, and no award decision is asserted.
