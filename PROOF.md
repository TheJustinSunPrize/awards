# Mathematical proof

We prove unbounded additive improvement, using the congruence construction idea
of Chen and Dai (2007), with factorials in place of products of primes.

Define d(0)=2 and d(i+1)=d(i)+(2d(i))!. The offsets are positive, even, and
strictly increasing. If i<=n and 0<m<=2d(i), every increment from d(i) to d(n)
is divisible by m. Thus m divides d(n)-d(i).

Fix r,M>=0. Put D=d(r), P=(2D)!, K=(4+2M)P-D and N=2K^2. Then P>=D,
K is even, K>=3D, K>=M, and K>=2. The standard set at N is precisely
B=[1,K] union {2h:1<=h<=K}.

Adjoin E={2(K+d(i)):0<=i<r}. These are r distinct positive integers, all
greater than 2K and at most N, so |B union E|=|B|+r. We check all pairs.

Pairs inside B satisfy the required lcm bound: use lcm(a,b)<=ab for the small
elements and mixed pairs, and 2*lcm(2u,2v)<=4uv for two even elements.

Two elements of E share a factor 4. Their lcm is at most
(K+d(i))(K+d(j)) <= (K+D)^2 <= 16K^2/9 < 2K^2.

For an element a=2(K+d(i)) and b=2h from B, if h<=K-d(i), their lcm is at
most 2(K+d(i))h <= 2K^2. Otherwise write h=K-j, with 0<=j<d(i), and
set m=d(i)+j. Since 2<=m<=2d(i), m divides both P and D-d(i), so it divides
K+d(i). Subtracting m shows that it also divides K-j. Hence a and b have a
common divisor 2m>=4. Their lcm is at most
(K+d(i))h <= (K+D)K <= 4K^2/3 < 2K^2.

Finally, any remaining element h<=K of B divides 2h. Therefore lcm(a,h)
divides lcm(a,2h), and the bound just proved applies. All pairs in B union E
are admissible, and N>=M. This covers r=0 too, with an empty set E.

The proof deliberately avoids claiming Chen and Dai's quantitative rate, or
the sharp asymptotic formula for the extremal function.
