# Proof outline

The negative mathematical answer is already attributed to Liam Price and GPT-5.4 Pro. This document explains the square-block route used in this Lean package; it does not assert that it is a new route or identical step by step to their exposition.

1. Let `B_q` be the primes in `[q²,(q+1)²)`. Their cardinalities are unbounded: a uniform bound C would bound the sum of prime reciprocals by `C * sum_{q≥1} 1/q²`, contradicting its divergence. The finite initial intervals can be excluded, so for any K,Q there is a q ≥ Q with at least K primes in `B_q`.

2. For given k,N0, choose such a q with q ≥ 10¹² + N0 and at least k primes. Set M = q², J = floor(q/100), H = 2q+1, T = floor(M/4), and N = JM. Choose k increasing primes in the block. The arithmetic module proves M ≥ 64, 8H ≤ M, 8JH ≤ M, and N ≥ N0.

3. Remove residues 0 through floor(p/2)-1 for each selected p. Consider S = {jM+3T+s : 0 ≤ j < J, 0 ≤ s < T}. Every point lies in [1,N]. The bounds on H and J imply `JH + floor(p/2) ≤ 3T`. Hence for x in this window, `jp + floor(p/2) ≤ x < jp+p`, so its residue modulo p is in the retained half. This holds simultaneously for all selected primes.

4. The map (j,s) to jM+3T+s is injective, so |S| = JT. Since M ≥ 64, M < 10T, yielding N = JM < 10JT ≤ 10|remaining|.

5. The deliberately conservative threshold q ≥ 10¹² gives q ≤ 200J and J > 10,240,000. Thus 256q² < J³. Since p < (q+1)² ≤ 4q², we get p⁴ < (Jq²)³ = N³. Cubing and using p ≥ 1 gives p¹⁰ ≤ p¹² < N⁹. All rounding and arithmetic steps are handled with exact integers in Lean.

6. Taking epsilon = eta = 1/10 contradicts any proposed uniform k, including a version with an arbitrary lower threshold N0. The k = 1000 specialization gives the displayed fixed-prime-count counterexample.

The separate JSON witness and Python checker concern only one concrete k = 1000 instance. They are not a premise of the Lean universal theorems.
