# Price-parameter analysis for JSP-000039

This is an English exposition of the supplied derivation and the accompanying
Lean finite routing model. All prices `a,b,c` are nonnegative rational numbers.
The analysis concerns the fixed network below, not arbitrary networks.

## Network and reference flow

The source is `s`, internal vertices are `u,v,w`, and terminals are `t1,t2,t3`.
The demands are respectively `15,10,15`; their maximum is `15`. There are
exactly the following nine directed edges.

| Edge | Reference flow x | Unit price | Relaxed bound x + 15 |
| --- | ---: | ---: | ---: |
| s -> t1 | 10 | a | 25 |
| s -> t2 | 6 | b | 21 |
| s -> u | 24 | 0 | 39 |
| u -> t3 | 10 | c | 25 |
| u -> v | 14 | 0 | 29 |
| v -> t1 | 5 | 0 | 20 |
| v -> w | 9 | 0 | 24 |
| w -> t2 | 4 | 0 | 19 |
| w -> t3 | 5 | 0 | 20 |

One may take original capacities to equal `x`. The column `x+15` is the
relaxed bound on the unsplittable routing, and is called `capacity` in Lean.
The reference flow is nonnegative. Its conservation equations are

```text
s:  10 + 6 + 24 = 15 + 10 + 15 = 40
u:  24 = 10 + 14
v:  14 = 5 + 9
w:  9 = 4 + 5
t1: 10 + 5 = 15
t2: 6 + 4 = 10
t3: 10 + 5 = 15
```

An explicit fractional decomposition sends `10,5` units on the two paths
to `t1`, `6,4` on the two paths to `t2`, and `10,5` on the two paths to `t3`
listed below. This reproduces every edge value in the table.
Only three edges have potentially nonzero prices, so its cost is

```text
F(a,b,c) = 10a + 6b + 10c.
```

Lean definitions: `DGG.source`, `target`, `terminalNode`, `demand`, `baseFlow`,
`capacity`, `fractionalCost`. The explicit conservation equations are proved by
`conservation_source`, `conservation_u`, `conservation_v`, `conservation_w`,
`sink_one`, `sink_two`, `sink_three`. `flow_feasible` checks the relaxed
bound and `Dmax_is_max` bounds every demand by `15`.

## Paths and the finite model

Write E for the path through the terminal's designated priced edge, and Z
for its zero-price alternative. E remains a name even when its price is zero.

| Terminal | E | Z | Entire demand's E cost |
| --- | --- | --- | ---: |
| t1 | s -> t1 | s -> u -> v -> t1 | 15a |
| t2 | s -> t2 | s -> u -> v -> w -> t2 | 10b |
| t3 | s -> u -> t3 | s -> u -> v -> w -> t3 | 15c |

In the stated graph these are all source-to-terminal paths: the last edge
into `t1` is from `s` or `v`, into `t2` from `s` or `w`, and into `t3` from
`u` or `w`. The only path to `u` is `s -> u`, to `v` is `s -> u -> v`,
and to `w` is `s -> u -> v -> w`. Terminals have no outgoing edges.
The ordering `s,u,v,w,t1,t2,t3` places every edge forward, so there are no
cycles and no additional walks formed by cycling.

This paragraph is a human graph argument. **The Lean source does not prove
this exhaustiveness from edge endpoints.** It defines `Choice.E/Z`,
`Route := Terminal -> Choice`, the edge-incidence table `uses`, and
`pathEdges`. Its theorem `path_complete` only says that `pathEdges t c`
belongs to `listedPath t`. It neither quantifies over arbitrary graph walks
nor connects `uses` with list membership in `pathEdges`.

The following Lean feasibility and optimization theorems are universal over
this explicitly specified finite `Route` model. The graph interpretation
requires the above correspondence, still pending formalization and review.

## Exhaustive capacity analysis

An unsplittable choice sends all of a terminal's demand on its chosen path.
`DGG.load` sums the three contributions for each edge; `DGG.Feasible r`
means every such load is at most `x+15`.

Any two Z choices are incompatible:

1. If `t1,t2` both use Z, the load on `s -> u` is `15+10+15=40>39`.
   The last `15` is unavoidable because both paths to `t3` use this edge.
2. If `t1,t3` both use Z, the load on `u -> v` is at least `15+15=30>29`.
3. If `t2,t3` both use Z, the load on `v -> w` is `10+15=25>24`.

Thus at most one terminal uses Z. All four remaining choices are feasible.
The following complete load table checks every edge, including zero loads.

| Edge | Bound | EEZ | EZE | ZEE | EEE |
| --- | ---: | ---: | ---: | ---: | ---: |
| s -> t1 | 25 | 15 | 15 | 0 | 15 |
| s -> t2 | 21 | 10 | 0 | 10 | 10 |
| s -> u | 39 | 15 | 25 | 30 | 15 |
| u -> t3 | 25 | 0 | 15 | 15 | 15 |
| u -> v | 29 | 15 | 10 | 15 | 0 |
| v -> t1 | 20 | 0 | 0 | 15 | 0 |
| v -> w | 24 | 15 | 10 | 0 | 0 |
| w -> t2 | 19 | 0 | 10 | 0 | 0 |
| w -> t3 | 20 | 15 | 0 | 0 | 0 |

Lean proves these facts in `routeEEZ_data`, `routeEZE_data`, `routeZEE_data`,
`routeEEE_data`, and `feasible_routes`. The latter states, for every `r`,

```text
Feasible r iff r = EEZ or r = EZE or r = ZEE or r = EEE.
```

`enum_charged` derives that at least two E choices occur. These conclusions
are proved by case analysis and arithmetic, not assumed as hypotheses.

## Exact minimum and budget quantifiers

The costs of the four feasible choices are respectively

```text
A = 15a + 10b
B = 15a + 15c
C = 10b + 15c
D = 15a + 10b + 15c.
```

Nonnegative prices imply `D >= A,B,C`, so the exact minimum is

```text
M(a,b,c) = min(A, min(B,C)).
```

`minUnsplitCost` defines this expression; `minUnsplitCost_lower_bound`
proves `M <= routeCost a b c r` for every feasible route and nonnegative
prices. `minUnsplitCost_attained` constructs a feasible route attaining the
expression. For every rational budget `q`, `feasible_prices_iff` proves

```text
(exists r, Feasible r and routeCost a b c r <= q) iff M(a,b,c) <= q.
```

The costs here are explicitly defined by `fractionalCost` and `routeCost`.
This version does not separately define a general sum of edge prices times
edge loads and prove its equality to those formulas.

## Strict counterexample conditions

By the lower bound and attainment, every feasible route costs strictly more
than `F` exactly when `F < M`. Expanding the minimum and subtracting terms
gives the following equivalence for all nonnegative rational `a,b,c`:

```text
F < M iff
  10c < 5a + 4b and
   6b < 5a + 5c and
  10a < 4b + 5c.
```

Lean: `DGG.counterexample_iff`. The graph-level conclusion follows from
the human correspondence arguments above; the complete conjecture has not
been encoded as a proposition in this project.

## Varying the middle price

Fix `a=c=2`, with `b` a nonnegative rational. Then

```text
F = 40 + 6b
M = min(30 + 10b, 60).
```

For `b <= 3`, strict inequality is equivalent to `b > 5/2`.
For `b >= 3`, it is equivalent to `b < 10/3`.
Their union is the exact open interval

```text
5/2 < b < 10/3.
```

At `b=5/2`, `F=M=55`; at `b=10/3`, `F=M=60`. Neither endpoint gives
a strict gap. Lean: `DGG.middle_price_iff` (the endpoint arithmetic in this
paragraph is explanatory, not a separately named theorem).

Taking `b=13/4` yields `F=119/2`, `M=60`, and `M-F=1/2`.
The feasible EZE choice attains `60`. These are proved by
`perturbed_fractional_cost`, `perturbed_minimum`, `perturbed_gap`, and
`perturbed_example`. Together with `feasible_prices_iff`, the proved facts
exclude a feasible finite-model route of cost at most `119/2`.

## Provenance and review

The supplied Chinese derivation is retained locally and was not overwritten.
Its SHA-256 is
`2f9cad03851de5d0d6fb6a736ecfe02650c36f7382c65604fd46bcd8de66ab2c`.
This English exposition corrects theorem names to the actual `DGG` namespace
and states the formalization gaps explicitly. It does not treat prose claims
in the supplied document as evidence that a Lean theorem has been proved.

The [official entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000039)
records discovery credit for Dmitry Rybin and formalization credit for Jason
Hickey, with links to the original sources. This package does not replace
those attributions or establish novelty, priority or award entitlement.
The public submitter is @linmanshan050813-dotcom. Independent verification,
statement-equivalence review, conflict review and recipient confirmation
remain pending.
