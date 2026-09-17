# JSP-000220: Erdős 252, irrationality of the sum of σ_k(n)/n! for k ≤ 2, and for all k under Hypothesis H

Catalog entry: [JSP-000220](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000220) · Problem source: [erdosproblems.com/252](https://www.erdosproblems.com/252)

## Problem

Let `σ_k(n) = ∑_{d ∣ n} d^k`. Is `∑_{n ≥ 1} σ_k(n)/n!` irrational for every `k ≥ 1`?

## Scope

Partial progress: the unconditional cases `k = 0, 1, 2`, the result for all `k` assuming Schinzel's Hypothesis H, and the result for `k ≥ 4` assuming the prime `k`-tuples conjecture. These are exactly the formal-conjectures variants `k_eq_zero`, `k_eq_one`, `k_eq_two`, `schinzel` and `prime_tuples`. The unconditional cases `k = 3` (Schlage-Puchta; Friedlander–Luca–Stoiciu) and `k = 4` (Pratt) are not formalized, and the full problem is not claimed. (An unrefereed full-proof claim by Tokengr1nder, using GPT 6 Astra, is listed on the erdosproblems.com forum; it is unrelated to this formalization.)

## Formal statements

All results are in `Erdos252.lean`. `erdos_252_sum`, `BunyakovskyCondition`, `SchinzelCondition` and all theorem statements are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/252.lean`, Apache-2.0). The two condition predicates are placed inside the namespace to avoid clashes; a check file confirms by `rfl` that they agree with the upstream definitions.

```lean
theorem erdos_252.variants.k_eq_one : Irrational (erdos_252_sum 1)

theorem erdos_252.variants.k_eq_two : Irrational (erdos_252_sum 2)

theorem erdos_252.variants.k_eq_zero : Irrational (erdos_252_sum 0)

theorem erdos_252.variants.schinzel (hs : ∀ (fs : Finset (Polynomial ℤ)),
    (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    Infinite ↑{n | ∀ f ∈ fs, Prime (Polynomial.eval (↑n) f).natAbs}) :
    ∀ k, Irrational (erdos_252_sum k)

theorem erdos_252.variants.prime_tuples {k : ℕ} (hk : 4 ≤ k) (hp : ∀ (a : Fin k → ℕ+)
    (b : Fin k → ℕ) (hab : ∀ p, p.Prime → ∃ n, ¬ p ∣ ∏ i, (a i * n + b i)),
    Set.Infinite {n | ∀ i : Fin k, (a i * n + b i).Prime} ) :
    Irrational (erdos_252_sum k)

theorem summable_sigma_div_factorial (k : ℕ) :
    Summable fun n => (σ k n : ℝ) / (n ! : ℝ)
```

The formal-conjectures statements `erdos_252.variants.k_eq_zero`, `k_eq_one`, `k_eq_two`, `schinzel` and `prime_tuples` are proved with their exact names and statements, and summability of the series is proved for every `k`, so each `tsum` is a genuine sum.

## Proof outline

For `k ≤ 2`: if the sum were `a/b`, choose a large prime `p = N + 1` and multiply by `N!`. The fractional part equals `σ_k(p)/p + σ_k(p+1)/(p(p+1)) + R` with `0 ≤ R ≤ 8/p`, which lies strictly between two consecutive integers (using `τ(n) ≤ n`, `2σ(n) ≤ n(n+1)`, `n² ≤ σ₂(n) ≤ 7n²/4`). For the conditional results, follow Friedlander–Luca–Stoiciu, Theorem 2, with one auxiliary prime `p > σ_k(k) + 2k`. Admissible linear forms `(cof i)·q_i − i` (from the prime tuples conjecture, or Hypothesis H applied to linear polynomials) give integers `n` where `n + i = cof(k,p,i)·q_i` with `q_i` prime for `1 ≤ i ≤ k`. Polynomial division of `(X+i)^k` by `(X+1)⋯(X+i)` and a tail bound `4(k+1)^k/(n+1)` show that the fractional part of `K·N!·∑` tends to `c/p ∉ ℤ` for an explicit `K`, which is a contradiction.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos252.erdos_252.variants.k_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos252.erdos_252.variants.k_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos252.erdos_252.variants.k_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos252.erdos_252.variants.schinzel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos252.erdos_252.variants.prime_tuples' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos252.summable_sigma_div_factorial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos252.lean` (`0b6927eaaee91d24b256048c3ef5f7c968b8714011bf7683b71740494ffecb68`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős and M. Kac [ErKa54] and P. Erdős and E. G. Straus [ErSt71, ErSt74] (the cases `k = 0, 1, 2`, as referenced in formal-conjectures); J. B. Friedlander, F. Luca, M. Stoiciu, *On the irrationality of a divisor function series*, Integers 7 (2007) [FLC07]; J.-C. Schlage-Puchta [ScPu06] (conditional results).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
