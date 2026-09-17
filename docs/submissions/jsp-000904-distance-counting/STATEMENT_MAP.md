# Statement map and claim boundary

The current catalog entry is
[JSP-000904](../../../problems/catalog-0901-1000.md#JSP-000904), corresponding
to Erdős Problem 1087. The table separates the original question from the
scoped results in this submission.

| Item | Treatment |
| --- | --- |
| Ambient space | A finite set of distinct points in the Euclidean plane. |
| Bad four-point subset | A four-set in which two different unordered edges have equal positive length; shared endpoints are allowed. |
| Original extremal function | `f(n) = max F(P)` over all planar `n`-point sets. |
| Target in the source problem | Prove `f(n) <= n^(3+o(1))`; not proved here. |
| Exact scoped result | The weighted count `W(P)` satisfies equation (1) of [PROOF.md](PROOF.md). |
| Weighted/unweighted comparison | `F(P) <= W(P) <= 10F(P)`, with a planar example attaining 10. |
| Published-theorem consequence | `F(P) = O_epsilon(n^(3.135862489727... + epsilon))`. |
| Equivalent blocker | The target is equivalent, using Guth--Katz, to `t(n) <= n^(2+o(1))` for distinguished-apex isosceles configurations. |
| Restricted class | `F(P) = O(n^3 log n + L n^3)` when every line contains at most `L` points; hence `O(n^3 log n)` when no three points are collinear. |
| General `n^(2+o(1))` isosceles bound | Not proved. |
| Complete solution, Lean proof, independent review, or award claim | Not claimed. |

The checker validates finite instances of the counting identities. It does not
replace the cited asymptotic theorems or establish the missing general bound.
