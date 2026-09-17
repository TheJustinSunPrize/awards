# Exact counting identity and scoped bounds

## 1. Definitions

Let `P` be a set of `n >= 4` distinct points in the Euclidean plane. Write
`E(P)` for the unordered two-element subsets of `P`.

For a four-point subset `S` of `P`, let `w(S)` be the number of unordered pairs
of distinct edges of `S` that have equal length. Define

\[
F(P)=\#\{S\subseteq P: |S|=4,\ w(S)>0\},
\qquad
W(P)=\sum_{\substack{S\subseteq P\\|S|=4}}w(S).
\]

Thus `F(P)` counts each bad four-set once, while `W(P)` counts every equality
between two different edges inside it.

Let

\[
T(P)=\#\{(a,\{b,c\}):a,b,c\in P\text{ distinct and }
             |a-b|=|a-c|\}.
\]

The apex `a` is distinguished and the base pair is unordered. Collinear
configurations, in which `a` is the midpoint of `b` and `c`, are included.

Finally, use the ordered distance-quadruple count from Guth--Katz:

\[
Q(P)=\#\{(a,b,c,d)\in P^4: |a-b|=|c-d|>0\}.
\]

The four entries of a member of `Q(P)` need not be distinct.

## 2. Exact identity

**Theorem 1.** For every planar `n`-point set `P`,

\[
\boxed{
W(P)=\frac{Q(P)-2n(n-1)}8+(n-4)T(P).
}
\tag{1}
\]

Moreover,

\[
\boxed{F(P)\le W(P)\le 10F(P).}
\tag{2}
\]

### Proof of the identity

Let `B(P)` be the number of unordered pairs of equal-length edges whose four
endpoints are all distinct. Two different equal-length edges either share one
endpoint or have four distinct endpoints. The first type is counted by `T(P)`
and the second by `B(P)`.

For each unordered edge of `P`, choosing an orientation independently in the
first and second positions gives four members of `Q(P)` in which the two
underlying edges are the same. This contributes

\[
4\binom n2=2n(n-1).
\]

Each unordered pair of different equal-length edges contributes eight ordered
quadruples: two orders for the edges and two orientations for each edge.
Therefore

\[
Q(P)=2n(n-1)+8\bigl(T(P)+B(P)\bigr).
\tag{3}
\]

An equal-edge pair with four distinct endpoints belongs to exactly one
four-point subset. An equal-edge pair sharing one endpoint uses three points and
belongs to each of the `n-3` four-point supersets of those points. Hence

\[
W(P)=B(P)+(n-3)T(P).
\tag{4}
\]

Eliminating `B(P)` between (3) and (4) gives (1).

### Proof of the comparison with `F(P)`

Every set counted by `F(P)` contributes at least one to `W(P)`, so
`F(P) <= W(P)`.

For a fixed four-point set, partition its six edges into equal-length classes
of sizes `m_1,...,m_k`. Four distinct planar points cannot have all six mutual
distances equal: after fixing two points at distance `r`, the only two points at
distance `r` from both are the two equilateral-triangle apices, and those two
apices are at distance `sqrt(3) r` from each other. Thus every class has size at
most five. Subject to `sum m_i = 6`, the maximum of
`sum binom(m_i,2)` is `binom(5,2)=10`. Consequently `w(S) <= 10` for every bad
four-set, proving `W(P) <= 10F(P)`.

The constant 10 is attained. For the four points

\[
(0,0),\quad(2,0),\quad(3,\sqrt3),\quad(1,\sqrt3),
\]

five squared distances equal `4` and the remaining squared distance equals
`12`.

## 3. Consequence of published general estimates

Guth and Katz prove

\[
Q(P)=O(n^3\log n)
\tag{5}
\]

for precisely the ordered quadruple convention above.

Katz and Tardos prove that, for every `epsilon > 0`, the number of
nondegenerate isosceles triangles determined by `P` is

\[
O_\epsilon(n^{\alpha+\epsilon}),
\qquad
\alpha=\frac{117-34e}{55-16e}
=2.135862489727\ldots,
\tag{6}
\]

where `e` is the base of the natural logarithm. Passing from unmarked
isosceles triangles to distinguished-apex configurations changes the count by
at most a factor of three. The degenerate configurations contribute at most
`binom(n,2)`, because an unordered base pair has at most one midpoint. Thus

\[
T(P)=O_\epsilon(n^{\alpha+\epsilon}).
\tag{7}
\]

From (1)--(2),

\[
F(P)\le W(P)\le \frac18Q(P)+nT(P).
\]

Combining this with (5) and (7) gives the unconditional bound

\[
\boxed{
F(P)=O_\epsilon
\left(n^{3.135862489727\ldots+\epsilon}\right).
}
\tag{8}
\]

This is a consequence of published estimates, not a proof of the conjectured
`n^(3+o(1))` bound.

## 4. Equivalent remaining estimate

Let

\[
f(n)=\max_{|P|=n}F(P),\qquad
t(n)=\max_{|P|=n}T(P).
\]

Interpret `f(n) <= n^(3+o(1))` as: for every `epsilon > 0`, there is a
constant `C_epsilon` such that `f(n) <= C_epsilon n^(3+epsilon)` for all
`n >= 4`, and analogously for `t(n)`.

**Theorem 2.** Using the Guth--Katz estimate (5),

\[
\boxed{
f(n)\le n^{3+o(1)}
\quad\Longleftrightarrow\quad
t(n)\le n^{2+o(1)}.
}
\tag{9}
\]

Indeed, (4) and (2) give

\[
F(P)\ge \frac{W(P)}{10}
       \ge \frac{n-3}{10}T(P).
\]

For `n >= 6`, this implies `T(P) <= 20F(P)/n`; the finitely many smaller
values can be absorbed into the constant. This proves the forward implication.

Conversely, (1), (2), and (5) give

\[
F(P)=O(n^3\log n)+nT(P).
\]

An `n^(2+o(1))` upper bound for `T(P)` therefore implies an
`n^(3+o(1))` upper bound for `F(P)`. This proves (9).

The unproved general estimate on the right side of (9) is the precise blocker
left by this reduction.

## 5. A bounded-collinearity special case

For each unordered pair `{b,c}`, let `ell_bc` be its perpendicular bisector.
Then

\[
T(P)=\sum_{\{b,c\}\in E(P)} |P\cap\ell_{bc}|.
\tag{10}
\]

If every line contains at most `L` points of `P`, equation (10) gives

\[
T(P)\le L\binom n2.
\]

Together with (5), this yields

\[
\boxed{F(P)=O(n^3\log n+Ln^3).}
\tag{11}
\]

In particular, if no three points of `P` are collinear, then `L <= 2` and

\[
\boxed{F(P)=O(n^3\log n).}
\tag{12}

This settles the target upper bound only for that restricted class of point
sets. The original problem imposes no collinearity restriction.
