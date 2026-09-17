# JSP-000744: Erdős 893, Kovač–Luca: the doubling ratios f(2n)/f(n) of f(n) = Σ τ(2^k − 1) are unbounded

Catalog entry: [JSP-000744](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000744) · Problem source: [erdosproblems.com/893](https://www.erdosproblems.com/893)

## Problem

Let `τ(n)` count the divisors of `n` and `f(n) = ∑_{1≤k≤n} τ(2^k − 1)`. Does `f(2n)/f(n)` tend to a limit?

## Scope

Partial progress: the theorem of Kovač and Luca (arXiv:2506.04883, 2025) that `limsup f(2n)/f(n) = ∞`, i.e. there is no finite limit; this is the formal-conjectures variant `erdos_893.variants.unbounded`. Whether `f(2n)/f(n) → ∞` (the formal-conjectures statement `erdos_893`, still open) and the conditional results of Kovač–Luca are not formalized or claimed.

## Formal statements

All results are in `Erdos893.lean`. `f` and the statement of `erdos_893.variants.unbounded` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/893.lean`, Apache-2.0).

```lean
theorem erdos_893.variants.unbounded :
   ¬ BddAbove (Set.range fun n : ℕ => (f (2 * n) : ℝ) / f n)

theorem exists_prime_orderOf_two_eq {a d : ℕ} (hd : 1 < d) (hda : d ∣ 14 ^ a) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = d

theorem two_pow_le_sigma_zero (a : ℕ) :
    2 ^ ((a + 1) * (a + 1) - 1) ≤ σ 0 (2 ^ (14 ^ a) - 1)
```

`erdos_893.variants.unbounded : ¬ BddAbove (Set.range fun n : ℕ => (f (2 * n) : ℝ) / f n)` is proved with its exact formal-conjectures name, statement and definition of `f`. Along the way: for `1 < d ∣ 14^a` there is a prime `p` with `orderOf (2 : ZMod p) = d`, and `τ(2^(14^a) − 1) ≥ 2^((a+1)^2 − 1)`.

## Proof outline

For `1 < d ∣ 14^a` take a prime `p ∣ Φ_d(2)` (Mathlib: `|Φ_d(2)| > 1`). Then `2^d ≡ 1 (mod p)`, `p ≠ 2`, and `p ≠ 7` because 2 has order 3 modulo 7 and `3 ∤ d`; so `p ∤ d` and 2 has order exactly `d` modulo `p`. These primes are distinct for distinct `d` and all divide `2^(14^a) − 1`, so `τ(2^(14^a) − 1) ≥ 2^((a+1)^2 − 1)`. If `f(2n)/f(n) ≤ C` for all `n`, then `f(2^m) ≤ C^m` (as `f(1) = 1`), and `2^((b+1)^2 − 1) ≤ f(2^(4b)) ≤ (C^4)^b` since `14^b ≤ 2^(4b)`, which fails for large `b`. The final step is Kovač–Luca's; the lower bound on `τ(2^k − 1)` along `k = 14^a` replaces their use of Bang's theorem and highly composite numbers.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos893.erdos_893.variants.unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos893.exists_prime_orderOf_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos893.two_pow_le_sigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos893.lean` (`51adab8114d5a0d138e264936adc8993f12a7db13f819bb37cf6f7d6c9278a7a`) are in `verification/`.

## Attribution

- Mathematics: V. Kovač and F. Luca, *On the number of divisors of Mersenne numbers*, arXiv:2506.04883 (2025) [KoLu25], Theorem 1, building on a heuristic of S. Cambie, as cited by the catalog record JSP-000744 and erdosproblems.com/893. Problem from P. Erdős [Er98]. The simplified route to the divisor lower bound (the family `k = 14^a` with cyclotomic primitive prime divisors) was found during the formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
