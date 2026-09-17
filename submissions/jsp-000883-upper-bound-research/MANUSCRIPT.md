# A proposed lcm-scale upper bound for Erdos Problem 1063

Research note v0.1 | 17 September 2026

Published by the GitHub account **randyxian08**, with OpenAI ChatGPT/Codex assistance.
This is an unrefereed proof claim offered for scrutiny. No completed Lean proof,
established first-discovery priority, or award decision is claimed.

For `k>=2`, put `L_k=lcm(1,...,k-1)`. Let `n_k` be the least `n>=2k` for which exactly one of `n,n-1,...,n-k+1` fails to divide `binom(n,k)`, whenever such an `n` exists. We propose that, eventually,

$$
n_k\le3L_k.
$$

This implies `n_k=O(L_k)` and `L_k=o(kL_k)`, the two requirements of the `better_upper` target. We construct actual admissible values before invoking a least value, avoiding any use of the empty-set convention for a natural infimum.

## The finite construction

Assume `k>=9`, `p` prime, `k<2p`, and `3p+2<=2k`. Set

$$
L=L_k,\qquad m=kL/p,\qquad r=m\bmod p,\qquad s=k-p-1.
$$

Choose `n=m` when `r<=s`, and `n=m+k-1` otherwise. We prove that the unique exception in the resulting interval is `m`.

Because `p<k<2p` and `p^2>k`, we have `p∤k` and `v_p(L)=1`. Thus `m` is integral, `p∤m`, and `1<=r<=p-1`. Also `2p|L`: both 2 and the odd prime p occur among the integers whose least common multiple is L. Consequently `m>=2k`, and both intervals have positive elements and satisfy the required endpoint condition.

The hypothesis on p gives `2s>=p`. If `r<=s`, use the left interval `B={m-k+1,...,m}`. The two distinct multiples `m-r` and `m-r-p` lie in it since `r+p<=s+p=k-1`.

Otherwise `r>s`, whence `p-r<=s`. Use the right interval `B={m,...,m+k-1}`. It contains the two distinct multiples `m+(p-r)` and `m+(2p-r)` since `2p-r<=p+s=k-1`.

In both cases, B contains at least two p-multiples, and with `n=max B` we have

$$
C:=\binom nk=\frac{\prod_{d\in B}d}{k!}.
$$

## Primes other than p

Fix an arbitrary prime `q!=p` and put

$$
a=\max_{1\le j<k}v_q(j),\qquad b=v_q(k),\qquad A=\sum_{j=1}^{k-1}v_q(j).
$$

Then `v_q(m)=a+b` and `v_q(k!)=A+b`. Write the interval as

$$
B=\{m\}\cup\{m+\varepsilon j:1\le j<k\},\qquad \varepsilon\in\{-1,1\}.
$$

For every j, the valuation inequality gives `v_q(m+epsilon j)>=v_q(j)`. Therefore, for `d_i=m+epsilon i`,

$$
\begin{aligned}
v_q\left(\prod_{d\in B\setminus\{d_i\}}d\right)
&\ge a+b+A-v_q(i)\\
&\ge A+b=v_q(k!).
\end{aligned}
$$

It follows from `C k! = prod B` that `v_q(C)>=v_q(d_i)`. This argument covers every prime `q!=p`, including primes larger than k; no factorization of large interval members is being assumed to involve only small primes.

## The prime p

We have `v_p(k!)=1`. Removing any one element from B leaves at least one p-multiple, because B contains at least two distinct ones. Consequently `v_p(C)>=v_p(d)` for every `d in B`.

Together with the previous paragraph, this proves `d|C` for every `d in B` other than m.

## The exception is genuine

Choose a prime divisor q of k. It is not p. In the preceding notation `b>0`, so

$$
v_q(m)=a+b>a\ge v_q(j)\qquad(1\le j<k).
$$

Unequal valuations imply exact equality `v_q(m+epsilon j)=v_q(j)`. Hence

$$
v_q(C)=(a+b)+A-(A+b)=a<v_q(m).
$$

Thus `m∤C`, proving that there is exactly one exception. Its descending offset is 0 for the left interval and `k-1` for the right interval.

Finally,

$$
n\le kL/p+k-1<2L+k-1\le3L,
$$

using `p>k/2` and `L>=k-1`.

## The eventual bound

The established prime number theorem gives

$$
\pi\left(\frac{2k-2}{3}\right)-\pi\left(\frac{k}{2}\right)
=\left(\frac16+o(1)\right)\frac{k}{\log k}>0
$$

for every sufficiently large k. Thus a suitable prime p exists eventually. Applying the finite construction yields an actual witness and `n_k<=3L_k` for all sufficiently large k.

Choose `U(k)=L_k`. We obtain `n_k=O(U(k))`, and because `L_k>0`,

$$
\frac{U(k)}{kL_k}=\frac1k\to0.
$$

This is the proposed improvement over the recorded `kL_k` comparator. No explicit threshold is claimed. Exact tests up to 300 are supporting evidence only, not a replacement for the all-parameter argument or its prime-number-theorem input.

See [REFERENCES.md](REFERENCES.md) for attribution, the inspected target, and the limits of the prior-art check. See [VERIFICATION.md](VERIFICATION.md) for actual computational results and incomplete Lean status. The proposed factor-k improvement does not determine the sharp asymptotic growth rate or claim to settle every interpretation of the original estimation problem.
