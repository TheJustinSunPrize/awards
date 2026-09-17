# Statement correspondence and proof

## The exact random walk and counted quantity

The state space is Z×Z. At time 0 the walk is at the origin. Each increment is independent and uniform over the four nearest-neighbor directions. The measure is the infinite product increment law pushed forward by partial summation, defined in the retained `ErdosProblems/Erdos1165/Basic.lean`.

For a path s define:

- Lₙ(x) = #{k : 0≤k≤n and s(k)=x}.
- Mₙ = maxₓ Lₙ(x).
- Fₙ = {x : Lₙ(x)=Mₙ}, including all tied maximizers.
- Uₙ = the union of F₀,...,Fₙ, counting distinct sites, not visits or multiplicities.

`mem_favorites_iff` in `Counting.lean` characterizes favorites by comparison against every site, including unvisited sites. Since the initial visit makes the maximum positive, restricting the finite representation to visited sites loses no maximizer. `DefinitionBridge.lean` proves equality of the local times, visited sets, maxima, favorite sets and favorite counts with the upstream definitions.

The final theorem says that for almost every path, there exist C>0 and N such that for every n≥N, |Uₙ|≤C log²n. Both C and N may depend on the path. The statement is not merely an expectation estimate or a bound on |Fₙ|. The explicit positive-constant form and standard Mathlib big-O form are both proved.

## Deterministic counting

Assume |Fₖ|≤K for N≤k≤n. Group times in this interval by their maximum local time. Within a group the maximum stays fixed: any site that was a favorite earlier must remain a favorite at the group's last time. Therefore each group contributes at most K distinct sites. At most Mₙ positive maximum levels occur. Before time N, at most N distinct visited sites occur. Thus

```
|Uₙ| ≤ N + K Mₙ.
```

The Lean lemma is universal over arbitrary sequences into any type with decidable equality; it requires no probability law. It also covers N>n by a direct visited-site bound.

## Maximum-local-time bound

Choose a site attaining Mₙ and let j≤n be its first visit. Recenter the path from time j at that site. Every original visit up to n lies among the recentered path's first n+1 positions. For deterministic j, recentering preserves the random-walk law. A finite union bound therefore gives

```
P(Mₙ≥k) ≤ (n+1) P(Lₙ(0)≥k).
```

No independence of a randomly selected first-visit time is assumed. The union is over deterministic times and uses their individually proved distributional equality.

The retained upstream fixed-origin tail theorem gives, for n≥1 and k≥2,

```
P(Lₙ(0)≥k) ≤ (1 - 1/(100 log(n+1)))^(k-1).
```

Set kₙ=ceil(300 log²(n+1))+1. The inequality 1-u≤exp(-u) yields

```
P(Mₙ≥kₙ) ≤ (n+1) exp(-3 log(n+1)) = 1/(n+1)².
```

At n=0, probability≤1 supplies the bound. The series is summable, so the first Borel–Cantelli lemma implies Mₙ<kₙ eventually almost surely. For n≥2, bounding log(n+1) by 2 log n and absorbing the ceiling error gives Mₙ≤2000 log²n eventually. The constant 2000 is uniform over paths and is not claimed optimal.

## Eventual favorite bound and assembly

The upstream concrete asymmetric pair source yields `HasPlanarMaximumLowerDeviation simpleRandomWalk`. That proved input is supplied to `simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_lowerDeviation`; it is not introduced as an axiom or an undischarged assumption.

The definition bridge transfers the resulting almost-sure statement to Fₙ. Intersect it with the maximum-bound event under the same measure. For each resulting path and sufficiently large n,

```
|Uₙ| ≤ N_f + 3 Mₙ ≤ (N_f+6000) log²n.
```

The explicit positive-constant theorem is obtained by increasing a nonnegative big-O constant by 1. This does not change the asymptotic statement and avoids any hidden strict-positivity convention.

## Prior work and evidence boundaries

The public mathematical reduction is described at https://www.erdosproblems.com/history/1166. The HLOZ result is from *Favorite Sites for Simple Random Walk in Two and More Dimensions*, https://arxiv.org/abs/2409.00995. The classical maximum-local-time result is associated with Erdős–Taylor (1960); here an upper bound sufficient for the reduction is explicitly derived in Lean.

The same final theorem already has an upstream Lean implementation: see PRIOR_ART.md. This implementation does not claim to be first. The new root files are an alternative formal implementation, with substantial, attributed reuse of upstream probability theory. Local compilation, axiom audits and Lean-kernel replay do not substitute for an independent statement-fidelity review or the Prize Operator's eligibility decision.
