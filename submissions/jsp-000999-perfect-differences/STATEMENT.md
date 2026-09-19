# Exact formal statement

All arithmetic in the implementation is on natural numbers. The seed and completed set are restricted to positive elements by explicit hypotheses and conclusions.

`Sidon S` means: for every `a,b,c,e ∈ S`, if `a+b=c+e`, then either `(a=c and b=e)` or `(a=e and b=c)`. Repeated summands are allowed. This is the usual sum formulation of the Sidon property, equivalent for integer sets to uniqueness of nonzero differences.

`Represents A d p` means `p.1 ∈ A`, `p.2 ∈ A`, `p.2 < p.1`, and `p.1−p.2=d`. Although subtraction on naturals is truncated, the strict ordering and `d>0` recover the ordinary integer difference. `Perfect A` asserts positivity and exactly one such ordered pair for every `d>0`. Negative integer differences follow by swapping the pair; that extension to an integer-indexed representation function is not separately formalized.

Let `S` be a finite Sidon seed of positive integers, `k=|S|`, `M=max S` with `M=0` when empty, and

`bound(S,n) = M + 2*(k+2*n+1)^3`.

The theorem `finite_seed_completion` asserts the existence of a set `A ⊆ ℕ` with all of:

1. `S ⊆ A`.
2. `Perfect A`.
3. `A` is infinite.
4. For every `d>0` and every pair `p` representing `d` in `A`, `p.1 ≤ bound(S,d)`.
5. For every `n≥0` there is a finite `B ⊆ A` with `|B|=k+2*n` and every `a∈B` at most `bound(S,n)`.

The witnesses are `A=completion S` and `B=stage S n`; stages and their next pairs are computable. The empty-seed consequence `exists_perfect_cubic` gives `u(d) ≤ 2*(2*d+1)^3` without any nonempty-seed assumption. These are intentionally loose explicit constants.

## Two different growth quantities

`u(d)` denotes the larger element in the unique representation of the *difference* `d`. It is not the `d`-th smallest member of `A`. In Cilleruelo–Nathanson, Section 4.1, `t_d` is the smaller endpoint, so `u(d)=t_d+d`; the cubic bound has the same exponent. The existing `lechmazur/erdos_1194` project also indexes its top endpoint by the difference.

The counting witness is a separate density statement. In ordinary mathematical notation it yields a cube-root lower bound for `A(x)=|A∩[1,x]|` for sufficiently large `x`. The Lean package proves the exact finite-witness inequalities above, not a separate real-variable Big-Omega statement.

The full optimal endpoint growth, an `o(d^3)` endpoint construction, and the stronger density results of Cilleruelo–Nathanson are outside the statement. This is a formalization of an established construction direction, not a completed solution of the open problem.
