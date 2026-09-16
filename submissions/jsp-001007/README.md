# JSP-001007 — Lean 4 formalization of the Price–GPT half-residue sieve counterexample

Independent formalization submitted for intake and eligibility review.

## Problem (catalog record JSP-001007)

> How many integers can simultaneously avoid about half the residue classes modulo each of
> several primes?

Equivalently (Erdős problem #1202 / Ben Green, *100 open problems*, Problem 44): sieve `[N]`
by removing `(p i - 1)/2` residue classes modulo each of `k` primes below `N^(9/10)`; is the
remaining set always at most `N/10`?

## Result

**No.** `Jsp/Jsp001007Final.lean` proves, with no `sorry`, no `admit`, no `native_decide` and
no axioms beyond Lean/Mathlib's three standard ones:

```lean
theorem JSP001007.green44_counterexample (k : ℕ) [NeZero k] (hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧ StrictMono p ∧ (∀ i, (p i) ^ 10 < N ^ 9) ∧
      (∀ i, (A i).card = (p i - 1) / 2) ∧ N / 10 < (survivors N p A).card
```

i.e. for every `k ≥ 1` and all sufficiently large `N` there are `k` distinct primes below
`N^(9/10)` and forbidden class sets of size `(p i - 1)/2` leaving **more than `N/10`**
surviving integers in `[1, N]`.  This refutes the proposed bound for every `k`, hence answers
Green's Problem 44 and the stated counterexample case in the negative.

`Jsp/Jsp001007Conclusion.lean` additionally proves
`JSP001007.not_green44_conjecture : ¬Green44Conjecture (1/10 : ℝ)`,
including the empty-prime-list case and the integer/real bound conversions.

## Source

The mathematics is due to Liam Price and GPT-5.4 Pro,
*[A Counterexample to a Half-Residue Sieve Bound](https://www.overleaf.com/read/qyhdmrchqnvb)*
(the construction is reproduced from the public write-up).  No new mathematics is claimed; the
contribution is the formalization.

## Structure of the formalization

| File | Content |
| --- | --- |
| `Jsp/Jsp001007.lean` | definitions (`survivors`, admissibility), the conjecture and refutation statements |
| `Jsp/Jsp001007Proof.lean` | **combinatorial core** `counterexample_core`: for clustered primes with `6·(N/M)·D ≤ M` and `10M < 7N`, the block set `T = {jM+t}` survives and `|T| = K·L > N/10` |
| `Jsp/Jsp001007Chebyshev.lean` | **prime count input**: `(n, 2n]` contains `≥ n/(4 log 2n)` primes, via central binomial coefficients (`four_pow_lt_mul_centralBinom`, `centralBinom_eq_prod`, `pow_factorization_choose_le`) and Mathlib's Chebyshev bound |
| `Jsp/Jsp001007Cluster.lean` | **clustering**: `k` primes in `(n, 2n]` with span `≤ 1024 k² log (2n) + 4` (pigeonhole on blocks) |
| `Jsp/Jsp001007Final.lean` | numeric glue at `n = ⌊N^(9/10)/4⌋` and the final theorem |
| `Jsp/Jsp001007Conclusion.lean` | direct negation of the recorded conjecture at `ε = 1/10`, including `k = 0` |

Only the combinatorial core is reproduced from the write-up; the prime count bound, the
clustering lemma and the numerical assembly were formalized from scratch for this submission.

## Build

```bash
./verify.sh     # cache get + lake build + axiom audit + placeholder scan
```

Pinned: Lean `v4.35.0-rc1`, Mathlib `96f4f6ca6e9dcdb26fec36ec10fa90c7f424e94d`.
`evidence/build.log` and `evidence/axioms.log` record the reproduced build and axiom audit.
Independent nanoda checking and pinned tool revisions are recorded in `evidence/metadata.json`.
Run `bash verify-nanoda.sh` to rebuild the pinned exporter and independent checker,
export both final endpoints, and check them with the strict three-axiom allowlist.

## Scope

The formalization covers the counterexample and its consequences for every `k`.  It does not
formalize the positive result for primes below `N^(1/2)` (large sieve), and it makes no claim
of a new mathematical discovery.

## Status

Prepared by an independent contributor with AI assistance.  Not reviewed by the prize
curators; no award level, recipient status or payment is claimed.

First-party proof code is provided under [Apache-2.0](LICENSE).
Dependency licenses and attribution are preserved in [evidence/THIRD_PARTY.md](evidence/THIRD_PARTY.md).
