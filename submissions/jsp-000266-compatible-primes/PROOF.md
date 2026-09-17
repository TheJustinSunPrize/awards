# Mathematical proof

Write E(N) for reciprocal subset sums with denominators at most N. Every element of E(m) either omits m or is `x+1/m` for `x ∈ E(m−1)`. Hence E(m) is the union of E(m−1) and that translate. The two sets have the same cardinality. They overlap precisely when `1/m` is a difference of two preceding subset sums. Differences correspond exactly to signed coefficients in `{−1,0,1}`: subtract the two indicator functions in one direction, and separate positive from negative coefficients in the other. This proves the exact doubling equivalence.

For the extension, put `M=p^k` and suppose an admissible signed representation of `1/(mM)` exists. Multiply by M and separate denominators divisible by M. These denominators are exactly `Mj` with `1 ≤ j < m`. After cancellation, the identity becomes

`q := 1/m − sum_{j<m} w(Mj)/j = sum_{n<mM, M∤n} M*w(n)/n`.

Compatibility says `p ∤ num(q)`, so q is nonzero and its p-adic valuation is at most zero. Each nonzero term on the right has valuation

`k + v_p(w(n)) − v_p(n) > 0`,

because `p^k ∤ n`, while an integer coefficient has nonnegative valuation. The non-Archimedean inequality implies a nonzero sum of such terms has positive valuation. This contradicts the bound for q. Zero terms are handled separately: Lean's valuation convention at zero does not justify treating them as having infinite valuation. The argument applies even when `p ≤ m` or `p ∣ m`.

There are finitely many signed sums. If m is irreducible, all obstruction numerators are nonzero. Let B(m) be the maximum of their absolute values. An integer p greater than B(m) cannot divide any of them. Euclid's theorem supplies primes exceeding B(m) and any prescribed bound. Applying the extension at exponent one gives arbitrarily large multiples of m where exact doubling occurs.

Finally, E(N) contains E(N−1) at every step. At each irreducible index the cardinality doubles. Starting at E(0)={0}, induction yields `|E(N)| ≥ 2^|U∩[1,N]|`.

The extension and doubling arguments are known mathematics from BGMS; this package supplies an independent Lean implementation. The finite numerator cutoff is used to formalize eventual compatibility without importing analytic estimates or the paper's sharper harmonic-lcm bound. Concrete `4,2` and `4,23` checks use `decide +kernel`, and their conclusions are linked to the general extension theorem. Executable `#eval` results and Python experiments are supplementary and do not replace proof terms.
