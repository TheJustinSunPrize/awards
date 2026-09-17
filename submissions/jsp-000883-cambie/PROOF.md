# Proof of Cambie's upper bound

The mathematical result formalized here is due to Stijn Cambie. For a natural number `k ≥ 3`, set

\[
S=\{1,\ldots,k-1\},\qquad L=\operatorname{lcm}(S),\qquad N=kL,
\qquad q_j=k(L/j)-1\quad(j\in S).
\]

All least common multiples, divisions, subtractions, and divisibility relations are interpreted over the natural numbers.

Since `0 ∉ S`, we have `L > 0`. For every `j ∈ S`, `j ∣ L`, so `L/j` is an exact positive quotient and

\[
N-j=j q_j.
\]

The Lean proof uses the distributive law for multiplication over truncated natural subtraction and `j * (L/j) = L`. It does not treat natural subtraction as integer subtraction.

## Product formula for the binomial coefficient

The auxiliary theorem `choose_pred_eq_prod`, by induction on `t`, gives

\[
\binom{N-1}{t}=\prod_{j=1}^{t}q_j\qquad(0\le t\le k-1).
\]

Both sides are `1` for `t = 0`. The induction step uses Mathlib's identity

\[
\binom{N-1}{t+1}(t+1)
=\binom{N-1}{t}(N-1-t).
\]

Substitute `N-1-t = N-(t+1) = (t+1)q_{t+1}`, apply the induction hypothesis, and cancel the positive factor `t+1`. Mathlib's `Nat.choose_mul_right` then yields

\[
\binom Nk=L\binom{N-1}{k-1}
=L\prod_{j=1}^{k-1}q_j.
\]

Write `P` for this final product.

## Exactly one exception

For each `1 ≤ j < k`, we have `j ∣ L` and `q_j ∣ P`, hence

\[
N-j=j q_j\mid LP=\binom Nk.
\]

On the other hand, `q_j` and `k(L/j)` are consecutive natural numbers and therefore coprime. Since `k ∣ k(L/j)`, it follows that `k` is coprime to each `q_j`, and thus to their product `P`. If `N` divided `C(N,k)`, then `kL ∣ LP`. Cancelling the positive factor `L` would give `k ∣ P`; coprimality would then force `k = 1`, contradicting `k ≥ 3`. Therefore `N` does not divide `C(N,k)`.

## Witness and bound

Because `k ≥ 3`, `2 ∈ S` and consequently `2 ∣ L`. Together with `L > 0`, this gives `L ≥ 2` and `N ≥ 2k`. Choose the exceptional offset `i₀ = 0`. The preceding argument proves nondivisibility at offset zero and divisibility at every other offset below `k`.

Thus `N` belongs to the set defining `n k`; in particular, that set is nonempty. Applying `Nat.sInf_le` to this member gives

\[
n_k\le k\operatorname{lcm}(1,\ldots,k-1).
\]

For `k = 3`, the construction gives `L = 2`, `N = 6`, and `C(6,3) = 20`: both `5` and `4` divide `20`, whereas `6` does not. For `k = 2`, it gives `L = 1` and `N = 2 < 2k`, which is not an admissible witness. The formal theorem retains the assumption `k ≥ 3`.

The proof uses general induction, divisibility, and coprimality. Finite parameter checks do not replace the universally quantified theorem.
