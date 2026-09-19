# Proof

Write `B={a(0)<a(1)<...}` and `E(x)=|[1,x] \ B|` for integer `x`. Full block-product injectivity forces all terms to be at least 2: a zero would make two blocks starting there equal, and a one would make a two-term block equal to the other singleton.

Choose integers `N,m,r,t` with `m²≤N`, `r³≤N`, and `m<(t+1)²`. Let `A(x)=x−E(x)` count the terms at most `x`.

There are at least `A(m)−A(t)−1` consecutive two-term blocks all of whose terms lie in `(t,m]`. Their products lie in `(m,N]`. Likewise there are at least `A(r)−A(t)−2` consecutive three-term blocks all of whose terms lie in `(t,r]`. Their products also lie in `(m,N]`: the first two factors already have product greater than `m`, and the third is positive. When either lower bound is negative, use zero blocks; the displayed lower bounds remain valid.

Every such product is omitted from `B`, because equality to a sequence term would identify a block of length 2 or 3 with a singleton. Products in each family are distinct, and the two families are disjoint, because equal products would identify blocks of different lengths. These products are also disjoint from the `E(m)` omissions at most `m`.

Counting these three disjoint families yields

`E(N) ≥ E(m) + A(m)−A(t)−1 + A(r)−A(t)−2`

`       = m+r−E(r)−2*A(t)−3`

`       ≥ m+r−E(r)−2*t−3`.

This is the finite inequality. Notice that it cancels the omissions at the square-root scale rather than simply estimating them by density. That cancellation is what leaves a meaningful cube-root term.

Now put `m=floor(sqrt(N))`, `r=floor(cuberoot(N))`, and `t=floor(sqrt(m))`. If `B` has density one, then `E(r)=o(r)`, while `t=O(N^(1/4))=o(r)`. Therefore

`E(N) ≥ floor(sqrt(N)) + (1−o(1))*floor(cuberoot(N))`.

Removing the floors costs only a bounded additive error, so

`liminf (E(N)−sqrt(N))/N^(1/3) ≥ 1`.

The Lean proof uses an exact integer version. Given `k≥1`, density provides `R` such that `2*k*E(n)≤n` for all `n≥R`. For `N≥max(R³,(16*k)^12)`, the cube-root lower bound ensures `r≥R`. The elementary power estimate in `error_absorbed` proves `2*k*(2*t+3)≤r`. Combining these two inequalities with the finite bound gives

`k*floor(sqrt(N))+(k−1)*floor(cuberoot(N))≤k*E(N)`.

This holds for every `k`, and is the fully formalized asymptotic coefficient statement. The standard real-valued natural-density hypothesis is connected to its integer version in the same Lean file.

This proof does not show that the coefficient one in the cube-root term can be attained. In particular, it remains compatible with the open possibility of `E(N)=(1+o(1))*sqrt(N)`: the new term is lower order than the leading square root.
