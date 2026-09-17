# Citation

## English

**Candidate progress claim (draft, under preparation; no award implied).**

For the Graham problem JSP-000263 — minimizing |sum_{k=1}^n eps_k/k| over
eps_k in {-1,0,+1} with a nonzero sum — the candidate work contributes:

1. **Exact tabulation.** The exact minimum f(n) for n = 2..40, computed in
   exact integer arithmetic over L_n = lcm(1..n) by two independent
   algorithms: (a) direct enumeration of all 3^n sign vectors with exact
   rational arithmetic for n <= 13; (b) meet-in-the-middle: sorted
   signed-subsum arrays for each half, vectorized binary-search merge to
   obtain the minimum cross gap, for n <= 40. Both methods agree on all
   overlap (n = 2..13).

2. **Structural reduction.** f(n) equals the minimum adjacent gap of the
   sorted set of all 2^n subset sums of {L_n/k : 1 <= k <= n}, divided by
   L_n. This converts the signed-subsum question into a subset-sum gap
   problem.

3. **p-adic obstruction lemma (proved).** For each prime p with n/2 < p <= n,
   every nonzero signed subsum numerator m satisfies m = eps_p (L_n/p) (mod p)
   with eps_p in {-1,0,+1}; in particular m is not divisible by p whenever
   eps_p != 0. This explains the observed downward jumps of f(n) at primes.

4. **Asymptotic conjecture.** Empirical fit log_10 f(n) = -0.074 pi(n)^2 -
   1.23 with R^2 = 0.99, suggesting f(n) = exp(-Theta(n^2/log^2 n)).

Highlights of the computed values: f(13..16) = 1/40040; f(17..21) = 23/6126120;
f(27..30) = 1/174594420; f(31..36) = 11/386105756400; f(37) = 109/8010391989600;
f(38..40) = 1/452675714400 (about 2.2 x 10^-12).

No formal Lean statement has yet been produced for this progress claim; this
record is published as a draft observation candidate pending independent
verification.

## English (computation reproducibility)

Scripts (Python 3.10+, exact integer arithmetic, no floating point in the
comparison path): `fseq2.py` (incremental exact subset-sum set), `fseq5.py`
(numpy int64 sorted-array merge), `fseq_vmitm.py` (vectorized MITM). Total
runtime about 45 minutes on a 24 GB workstation; n >= 41 requires out-of-core
subset-sum gap computation. Data file `f_sequence.json` contains the exact
numerator/denominator pairs.
