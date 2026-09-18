# Proof outline and statement fidelity

## English

Write A_p = floor(log_p k), T_p = floor(log_p max(E,k-1-E)), and let sigma_p
count the levels a=1,...,A_p with E mod p^a < k mod p^a. Put
H_p = T_p - sigma_p, using truncated natural subtraction.

1. **Carries and covering** (`OneCarry.lean`). Kummer's theorem expresses the
   p-adic exponent of the binomial coefficient as a carry count. Above the
   window length k, a power dividing n-i automatically supplies a carry.
   Consequently it suffices to cover the truncated valuation below A_p.
   Adding a multiple of p^(A_p+H_p) preserves the low carries and supplies the
   missing H_p carries. The proof also bounds every noncenter valuation.

2. **Exactly one failure** (`FiniteConstruction.lean`). Choose a prime pstar
   dividing k. Its first carry is missing, so sigma_pstar < A_pstar. Requiring
   pstar^(A_pstar+1) to divide the center displacement makes the center's
   valuation strictly greater than that of the binomial coefficient. Thus the
   exceptional coordinate is proved to fail; it is not merely left unchecked.

3. **Anchors and simultaneous approximation** (`FiniteConstruction.lean`,
   `Simultaneous.lean`). Let S be 2k times the product of small-prime powers
   p^(A_p+H_p), exceptional large-prime squares p^2 (where k mod p < 2E), and
   the failure-prime power. For each remaining prime, partition residues into
   Q boxes. Q^d+1 residue vectors yield two in the same box, hence a multiplier
   1 ≤ m ≤ Q^d. The proof uses integer divisions, not numerical approximation.
   If QE ≥ k, the resulting n=E+Sm has the requisite first carry at each
   regular prime. All other prime cases are covered by the anchor lemmas.
   The factor 2k ensures n ≥ 2k.

4. **Coarse size estimates** (`SizeBounds.lean`). Split exceptional primes
   according to k/p ≤ M. Encode the first part injectively by (k/p,k mod p),
   obtaining at most 2EM possibilities. The second part lies below k/(M+1).
   Thus their number is at most 2EM+k/(M+1). With y=E, put
   C=E+2EM+k/(M+1) and B=3+2C. The anchor satisfies S ≤ 2 k^B, and a witness
   satisfies n ≤ 4 k^B Q^pi(k).

5. **Parameters and analytic estimate** (`Parameters.lean`,
   `AsymptoticBound.lean`). Set t=floor(k^(1/16)), E=floor(k/t^2)+1,
   Q=t^2, M=t. For sufficiently large k these satisfy all construction
   hypotheses and Ct ≤ 7k, Bt ≤ 17k. Since k<(t+1)^16 and log(t+1)=o(t),
   log 4 + B log k ≤ (log 2)k/4 eventually. Mathlib's Chebyshev estimate gives
   pi(k) ≤ 2 log(4) k/log k eventually; t^16≤k then gives
   pi(k) log Q ≤ (log 2)k/2. Hence n ≤ exp((3/4)log(2)k) eventually.

6. **Official target** (`Submission.lean`). The constructed witness bounds
   the actual natural infimum n_k. Mathlib proves
   2^(k-1) ≤ k*lcm(1,...,k-1). Exponential comparison therefore gives the
   required little-o relation, together with the big-O bound on n_k.

Every mathematical hypothesis used by the final theorem is discharged. The
final theorem has no assumptions about carry budgets, prime distribution,
existence of the constructed witness, or external mathematical conjectures.
It uses Mathlib's proved Chebyshev estimates, not the prime number theorem.
