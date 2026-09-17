# Statement and correspondence

`DistinctBlocks a` quantifies over *all* natural endpoints `u≤v` and `u'≤v'`. Equal products over the two nonempty closed index intervals imply equality of both endpoints. No restriction to fixed lengths is built into the hypothesis. This is the original block-injectivity condition, with indexing starting at zero. The theorem `two_le` proves that every sequence term is at least 2 from this condition alone.

For a strictly increasing `a`, `cut a ha N` is the first index at which `a` exceeds `N`. `le_iff_lt_cut` proves that `a(i)≤N` exactly when `i<cut(N)`. `deficit_add_cut` proves `E(N)+cut(N)=N`, using positivity. Consequently `cut(N)` is exactly the number of retained positive integers up to `N`.

`cubeRoot N` is the integer cube root. Its two defining inequalities and the inverse comparison are proved, not assumed.

The main statement `second_order_of_natural_density` assumes

`Tendsto (fun N => (cut(N):Real)/(N:Real)) atTop (nhds 1)`

and concludes the quantified integer inequality in README. The value of the ratio at zero is harmless for the limit at infinity.

The auxiliary `DensityOne` is the explicit condition: for each integer `k≥1`, eventually `k*E(n)≤n`. `densityOne_iff_tendsto` proves that this is equivalent to `E(n)/n → 0`; `densityOne_of_retained_ratio` connects it to the retained proportion tending to one. There is no extra quantitative rate of density convergence in the main theorem.

## Finite statement and threshold

Without any density assumption, `finite_second_order` proves, for all natural `N,m,r,t`,

`m*m≤N`, `r*r*r≤N`, `m<(t+1)*(t+1)` imply

`m+r ≤ E(N)+E(r)+2*t+3`.

In particular, for `m=floor(sqrt(N))`, `r=floor(cuberoot(N))`, and `t=floor(sqrt(m))`, the inequality holds for every `N`, including zero.

For any `k≥1`, if `2*k*E(n)≤n` for all `n≥R`, then `second_order_explicit` proves the main inequality for every

`N ≥ max(R^3,(16*k)^12)`.

This threshold is intentionally loose. It depends on the sequence's density modulus `R`; the package does not claim a universal effective onset independent of the sequence.

The result is necessary, not sufficient. It does not construct an infinite density-one sequence, and finite examples are not substitutes for the limit hypothesis or the universal proof.
