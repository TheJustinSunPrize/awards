# General four-prime lemma for Erdős 700 (JSP-000570)

Research manuscript, version 6, 2026-09-17. The local four-prime theorem has a Lean proof in `Erdos700/FourPrime.lean`; see the build and axiom records for its verified scope. The Maynard corollary below is a human-readable argument, not part of the Lean formalization. External peer review and historical priority remain unestablished.

## Claim

Let positive integers a,b,c obey b>=3a and c>=3b-a+1. Let P>=12c^3, and suppose P,P+a,P+b,P+c are all prime. Set N to their product and f(N)=min_{2<=k<=floor(N/2)} gcd(N,binom(N,k)). Then

    f(N)=P(P+a)(P+b).

Consequently Maynard's theorem gives infinitely many N with f(N)=N^(3/4)(1+o(1)), as justified at the end.

## Notation and Lucas digit table

Put

    S=a+b+c, T=ab+ac+bc, Z=abc;
    S1=b+c-3a, T1=bc-2a(b+c)+3a^2, A=a(b-a)(c-a);
    R=a+c-3b, B=(2b-a)c+2ab-3b^2, C=b(b-a)(c-b);
    D=3c-a-b, U=3c^2-2c(a+b)+ab, F=c(c-a)(c-b).

All entries in this normalized digit table are legal. Here a>=1, b>=3 and c>=9. More explicitly:

- 0<S<3c, 0<T<3c^2 and 0<Z<c^3.
- 0<S1<2c. Also T1=(b-2a)c-2ab+3a^2>=a(c-2b+3a)>0, while T1<bc<c^2.
- 1<=R<c, directly from c>=3b-a+1 and 3b>a. Thus the high digit R-1 may be zero.
- 0<B<2bc<2c^2. For the lower bound, write B=3b(b-a)+a^2+(2b-a)(c-3b+a)>0; here c-3b+a>=1 and b>=3a. For the upper bound, 2bc-B=a(c-2b)+3b^2>0 because c>2b.
- 0<U<3c^2, since a+b<c implies U>c^2; and 0<D<3c.
- 0<A,C,F<c^3.

Every fixed nonnegative digit displayed above is below P, including R-1=0 when R=1. Thus the residual digits x-A,x-B,x-F,x-D are nonnegative and below x, while every other displayed digit is also between zero and x-1.

| base x | low digit of N/x | middle digit | high digit | fourth digit |
| --- | --- | --- | --- | --- |
| P | Z | T | S | 1 |
| P+a | x-A | T1-1 | S1 | 1 |
| P+b | C | x-B | R-1 | 1 |
| P+c | x-F | U-1 | x-D | 0 |

For every relevant k, k/x<x^3: since P>=12c^3>=10c, we have N<=(P+c)^4<2P^4, and k<=N/2 gives k/x<P^4/x<=x^3. Thus if x does not divide binom(N,k), Lucas gives x|k and

    k/x=u*x^2+v*x+w,

where u,v,w obey the first three digit bounds in the corresponding row.

For another prime q=x+d, simultaneous nondivisibility implies q|k/x. Writing

    u*d^2-v*d+w=h*q,

polynomial division yields

    k/q=u*q^2+(v-3ud+h)*q+(2ud^2-dv-dh).                 (1)

For pairs starting from P+a, we have u<2c, v<c^2, |d|<c and h in {0,1} for upward pairs. Consequently the constant coefficient K=2ud^2-dv-dh satisfies |K|<6c^3, and the middle coefficient M=v-3ud+h satisfies |M|<8c^2. For upward pairs starting from P, the congruence below gives h=0, v=du+t, with 0<=t<c^2; then K=d(du-t) and M=t-2du have |K|<4c^3 and |M|<6c^2 because u<3c. Including a possible one-unit borrow from the low digit, all middle coefficients have absolute value <10c^2. All constant coefficients have absolute value <10c^3. Both are below q. Hence each normalization needs at most one borrow. Moreover

    q-10c^3>c^3,  q-10c^2>U-1,

because q>=12c^3, c>=9, and U<3c^2. Thus a negative constant coefficient for a target with fixed low digit C<c^3 immediately violates that low bound. A negative middle coefficient, after any required low-digit normalization, produces a digit exceeding the fixed target middle bound U-1.

For pairs starting from P, the congruence w=dv-d^2u+hq, with |dv-d^2u|<6c^3 and 0<=w<=Z<c^3, forces h=0.
For pairs starting from P+a and going upward, |dv-d^2u|<3c^3 and 0<=w<=q-d-A<q force h=0 or 1.

## Pair P+a and P

Let u<=S1,v<=T1-1. The congruence forces w=-a^2u-av mod P. Write L=a^2u+av. Then

    0<=L<=a^2*S1+a*(T1-1)=A-a^3-a<A-a.

The only possible residue if L>0 is w=P-L>P-A+a, larger than the allowed P+a-A. If L=0 then u=v=w=0 and k=0.

## Pair P+a and P+b

Put d=b-a>0. The two branches have w=dv-d^2u+hq, h=0 or 1.

If h=0, then v>=du. Write K=d(2du-v), M=v-3du. If K<0 the normalized low digit is q+K>C, impossible. Hence v<=2du. If u=0 all digits vanish. Otherwise M<0, so the high digit is u-1 and the middle digit is q+M. Their bounds give

    u<=R, 3du-v>=B.

But 3du-v<=2du<=2dR, and

    B-2dR=a(c-b)+a(b-a)+3(b-a)^2>0,

a contradiction.

If h=1, the upper bound on w gives du-v>=a(c-a)+1. Put t=du-v. In (1), K=d(ud+t-1)>0 and M=-2ud-t+1<0. The low, middle, and high digit bounds give respectively

    ud+t-1<=b(c-b),
    2ud+t-1>=B,
    u<=R.

The first two imply

    ud>=B-b(c-b)=d(c-2b),

so u>=c-2b. But R=c-2b-d, a contradiction.

## Pair P+a and P+c

Put d=c-a>0, h in {0,1}. In (1) let K=d(2du-v-h), M=v-3du+h. If K<0, then

    -K<=d(T1),
    F/d-T1=(c-a)(c+3a-2b)>0.

Thus -K<F and the low digit q+K exceeds q-F. If K>=0 then v+h<=2du, so M<=-du. For u>=1, the middle digit is q+M>U-1. If u=0, K>=0 forces v=h=0, hence w=0 and k=0.

## Pair P and P+b

Here h=0. Write v=bu+t,w=bt with 0<=t<=ac. The constant and middle coefficients are

    K=b(bu-t), M=t-2bu.

If K<0 the low digit q+K exceeds C. Otherwise t<=bu. The u=0 case gives k=0; for u>=1, M<0. The low, middle, and high digit bounds imply

    bu-t<=(b-a)(c-b),
    2bu-t>=B,
    u<=R.

But

    2bu-t=bu+(bu-t)<=bR+(b-a)(c-b)=B-b^2<B,

a contradiction.

## Pair P and P+c

Again h=0, and v=cu+t,w=ct, 0<=t<=ab. The constant and middle coefficients are

    K=c(cu-t), M=t-2cu.

If K<0, then -K<=abc<F because c>a+b. Thus the low digit q+K exceeds q-F. If K>=0 and u>=1, then M<=-cu<0, giving middle digit q+M>U-1. If u=0, K>=0 forces t=0 and k=0.

## Pair P+b and P+c

Put d=c-b and L=b(b-a), so C=dL. We use L<c^2 and C<F, not L<d.
The latter strict inequality follows from F-C=(c-b)^2(c+b-a)>0.
Here 0<=u<=R-1<c, v<=x-B<x<q, w<=C<c^3. When R=1, u=0; this case remains covered below. In particular
ud^2+w<2c^3<q, giving

    -dq<ud^2-vd+w<q.

Consequently h=-H for H in {0,...,d-1}. Put J=(Hq+w)/d, which is an integer because v=ud+J. Formula (1) becomes

    k/q=u*q^2+(J-2ud-2H)*q+K,
    K=ud^2-w+dH.

We have -c^3<K<c^3+c^2<2c^3: use 0<=u<c, 0<=H<d<c, and 0<=w<=C<c^3. Normalizing the low digit introduces epsilon in {-1,0}; the middle coefficient becomes

    E=J-2ud-2H+epsilon.

If H>=1, the bounds on u,H,w give

    q/d-4c^2 <= E <= q-q/d+c^2.

Since q/d>=P/c>=12c^2>7c^2, this interval lies strictly between U-1 and q. So E is already the actual middle digit and is too large.

If H=0, write w=dt with 0<=t<=L. Then K=d(ud-t) and the middle coefficient is M=t-2ud.

- If K<0, then -K=w-ud^2<=w<=C<F. The actual low digit q+K therefore exceeds q-F.
- If K>=0 and u>=1, then t<=ud, so -2ud<=M<=-ud<0. The low coefficient has no borrow, and the middle digit q+M exceeds U-1 by the large-base margin.
- If K>=0 and u=0, then t=0, hence w=0 and k=0.

Thus this argument does not require d>L. All congruence and coefficient bounds
instead follow from L<c^2, w<=dL<c^3, and the existing large-base hypothesis.

## Conclusion of the local lemma

All pairs are excluded, so at least three of the four primes divide every relevant binomial coefficient. Their product is at least P(P+a)(P+b). Equality occurs at k=P+c: the three smaller primes divide binom(N,k) by their units digits, and Lucas gives binom(N,P+c)=N/(P+c) mod (P+c), nonzero. The value k=P+c lies below N/2.

## Infinite-family consequence

For any sufficiently large K, take H={h1,...,hK}, with h1=16 and h_{j+1}=h_j^4. These are powers of 2. The set is admissible: modulo 2 it misses 1, and modulo every odd prime it misses 0.

For any i<j<k<l, put a=h_j-h_i, b=h_k-h_i, c=h_l-h_i. Then

    b>h_j^4-h_j>3h_j>3a,
    c>h_k^4-h_k>10h_k^2>10b^2.

The displayed bounds on these chosen offsets imply the new hypothesis,
because 3b-a+1<=3b+1<=10b^2 for b>=3.

Maynard's theorem (with at least four prime values in a sufficiently large fixed admissible tuple), followed by the finite pigeonhole principle, produces one fixed quadruple of indices for infinitely many translates x. Letting P=x+h_i, the corresponding four primes satisfy the lemma for every sufficiently large such P. Their product N tends to infinity, and the lemma gives

    f(N)=P(P+a)(P+b)=N^(3/4)(1+o(1)).

This improves the exponent 2/3 of the inspected prior three-prime manuscript. It does not solve the separate characterization questions included in Erdős 700. Novelty across all literature remains to be established before claiming priority.

## Prior work and attribution

The current [Erdős 700 page](https://www.erdosproblems.com/700) credits the preceding three-prime construction to GPT 5.6 Sol Pro prompted by Liam Price. Its full public manuscript, [Large Binomial GCDs](https://www.overleaf.com/read/pmnwkfnhhxhn#82956e), proves a three-prime criterion and derives an infinite family with exponent 2/3. The present work extends the prime-product approach to four primes.
Version 4 lowered the final gap to c>=3b-a+1; version 5 reduces the base-size condition to P>=12c^3. Neither refinement changes the exponent. The use of Lucas digits and the strategy of combining a local criterion with Maynard are credited to those predecessors. No first resolution of the square-root infinitude question is claimed.

The proposed new contribution is the four-prime local criterion, its Lean formalization, and the separate stronger infinite-family consequence. This is not a complete solution of every part of Erdős 700.

References:

- P. Erdős and G. Szekeres, *Some number theoretic problems on binomial coefficients*, Australian Mathematical Society Gazette 5 (1978), 97–99. [Primary scan](https://www.renyi.hu/~p_erdos/1978-46.pdf).
- James Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015), 383–413, Propositions 4.2 and 4.3. [Publisher](https://annals.math.princeton.edu/2015/181-1/p07).
- [Formal Conjectures #700](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/700.lean) for the precise minimum convention. The local project defines this function independently and does not import the conjecture file or its unfinished declarations.

The mathematical exploration, proof implementation, and internal audits used OpenAI Codex. Parallel AI reviews are internal checks, not external peer review or official prize verification.

## Formal boundary obstruction

The separate [counterexample note](counterexample-formal.md) proves that
replacing c>=3b-a+1 by c>=3b-a fails even under P>=100c^5. Version 6
formalizes the four particular primalities, the valid witness index,
the exact gcd at that index, and the strict inequality for f(N). This
does not refute the sufficient condition proved above, calculate the exact
counterexample minimum, or establish an optimal more general condition.
