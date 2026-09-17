# Proof of the greedy construction

For a finite stage `S`, write `k=|S|`. Its finite difference set includes all natural truncated differences, including zero when `S` is nonempty. Let `d` be its least missing positive integer. Since there are at most `k^2` differences, `1≤d≤k^2+1`.

We adjoin a pair `x,x+d`. To retain the Sidon property it suffices to avoid the following three finite families for `x`:

- `a+b−c−e*d`, for `a,b,c∈S` and `e∈{0,1}`;
- `floor((a+b−e*d)/2)`, for `a,b∈S` and `e∈{0,1,2}`;
- `a+j*d−i*d`, for `a∈S`, `i∈{0,1,2}`, `j∈{0,1}`.

In this displayed description, subtraction is evaluated sequentially as truncated natural subtraction, exactly as in the Lean definitions. This may forbid extra values, which is harmless. A positive solution of any collision equation is still in the corresponding forbidden family; this is proved by `avoid_one`, `avoid_two`, and `avoid_shift`.

The union has cardinality at most `2*k^3+3*k^2+6*k`. Choose `x` as its least missing positive integer. The finite pigeonhole argument yields `x≤2*k^3+3*k^2+6*k+1`. The third family also ensures that both new elements are outside `S`; they are distinct because `d>0`.

To check a sum equality in the extended set, each of its four entries is either `x`, `x+d`, or an old element. The finite proof examines these cases. Two entirely old pairs use the old Sidon property. Two old summands against one or two new summands are excluded by the first two families. Comparisons involving one old summand use the third family, or would make `d` an old difference. Purely new sums have the required unordered uniqueness since `d>0`. This establishes `sidon_insert_pair` without a search oracle or a problem-specific axiom.

The new endpoint satisfies

`x+d ≤ 2*k^3+4*k^2+6*k+2 ≤ 2*(k+1)^3`.

Iterating from the seed gives nested stages with exactly `k+2*n` elements at stage `n`. The least-missing rule proves that all differences `1,...,n` occur by that stage. Induction using the endpoint estimate gives every stage element the bound `M+2*(k+2*n+1)^3`.

Take the union of all stages. Positivity and seed inclusion are immediate. Any four elements lie in a common finite stage, so sum uniqueness passes to the union. Every positive difference is represented by its own numbered stage. Converting an equality of two positive differences to a sum equality proves uniqueness; the crossed equality would force the positive difference to be zero.

For difference `d`, the pair already present at stage `d` satisfies the cubic endpoint bound. Its uniqueness means the same bound applies to every representation in the completed set. Stage `n` itself supplies the stated counting witness. Representing difference `N+1` supplies an element greater than `N`, proving infinitude.

The finite seed assumption and positivity are explicit. Non-Sidon seeds such as `{1,2,3}` cannot be repaired by adding elements, and the implementation is not claimed to do so. Mathematical attribution and the distinction from stronger existing results are in [PRIOR_ART.md](PRIOR_ART.md).
