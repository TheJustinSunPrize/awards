# Exact scope

All arithmetic in the proof is exact. Subset sums lie in `ℚ`; indices and exponents lie in `ℕ`; signed coefficients lie in `ℤ`.

`Small m w` means `−1 ≤ w(j) ≤ 1` for every integer `1 ≤ j < m`. Values of `w` outside this interval are irrelevant. `signedSum m w` is the sum of `w(j)/j` over that interval.

`Irreducible m` means `m > 0` and no admissible signed sum equals `1/m`. This is the BGMS set U, not the algebraic notion of an irreducible element.

`Compatible m p` means the integer `p` divides none of the **reduced** numerators of `1/m − signedSum m w`, for all admissible `w`. Primality is a separate hypothesis of the extension theorem. A zero numerator is divisible by every `p` and therefore rules out compatibility. The executable `isCompatible` only tests compatibility, not primality.

`sumsBelow m` is the image of the powerset of the natural interval `Ico 1 m` under reciprocal summation. Thus its cardinality is `S(m−1)` for positive `m`. Our `S N` is defined as `(sumsBelow (N+1)).card`, so it exactly counts the subsets of denominators `1,...,N`. Equal rational values are identified; subsets themselves are not counted. `S 0 = 1` includes the empty sum.

## Main proved statements

1. `compatible_prime_extension`: for all `m > 0`, primes `p` and `k ≥ 0`, compatibility implies `Irreducible (m*p^k)`. It does not require a separate irreducibility hypothesis on `m`, because compatibility itself rules out a zero obstruction.
2. `irreducible_iff_doubling`: for every `m > 0`, irreducibility is equivalent to `S(m) = 2*S(m−1)`.
3. `compatible_prime_doubling`: combines the preceding two statements for arbitrary `m,p,k`.
4. `doubling_count_lower_bound`: `S(N) ≥ 2^|U∩{1,...,N}|` for all `N ≥ 0`, with U recognized by a proved finite test.
5. `compatible_of_large`: if `m ∈ U`, every natural `p` greater than `numeratorBound m` is compatible. The bound is the maximum absolute reduced numerator over the finite obstruction set.
6. `exists_large_compatible_prime` and `exists_large_doubling_multiple`: every irreducible seed admits compatible primes and divisible exact-doubling indices beyond any prescribed bound. The latter has quantifiers `∀ B, ∃ n > B, m ∣ n ∧ S(n)=2*S(n−1)`.
7. `isIrreducible_correct` and `isCompatible_correct`: the executable Boolean tests are equivalent to the original quantified predicates.

The main extension includes the case `k = 0`. `m = 0` is excluded from it. The Boolean irreducibility test returns false at zero. No arithmetic expression involving division by zero is used to represent a valid positive denominator in the main statements.

## Excluded claims

No matching asymptotic upper bound, BGMS iterated-logarithm lower bound, explicit prime-counting estimate, or full solution of the catalog problem is proved here. The sharper BGMS cutoff `lcm(1,...,m)*H_m` is not formalized: we use a separately defined finite numerator cutoff. No claim is made that compatibility is necessary for all doubling extensions. The existence result has arbitrary-large quantifiers; a quantitative density of doubling indices is not claimed.
