# JSP-000230: Erdős 267, the case c ≥ 2 (Badea) and Badea's irrationality criterion

Catalog entry: [JSP-000230](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000230) · Problem source: [erdosproblems.com/267](https://www.erdosproblems.com/267)

## Problem

Let `F_n` be the Fibonacci numbers and `n_1 < n_2 < ⋯` with `n_{k+1}/n_k ≥ c > 1`. Must `∑_k 1/F_{n_k}` be irrational?

## Scope

Partial progress: the case `c ≥ 2` (Badea) and Badea's irrationality criterion. The range `1 < c < 2` is open and not claimed.

## Formal statements

All results are in `Erdos267.lean`. Statement shapes follow Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/267.lean`, Apache-2.0).

```lean
theorem erdos_267.variants.two_le : ∀ᵉ (n : ℕ → ℕ) (c ≥ (2 : ℚ)), StrictMono n →
    (∀ k, c ≤ n (k+1) / n k) → Irrational (∑' k, 1 / (Nat.fib <| n k))

theorem badea_criterion (a : ℕ → ℕ) (h : ∀ᶠ k in atTop, a k ^ 2 - a k + 1 < a (k + 1)) :
    Summable (fun k => 1 / (a k : ℝ)) ∧ Irrational (∑' k, 1 / (a k : ℝ))

theorem summable_of_two_le : ∀ᵉ (n : ℕ → ℕ) (c ≥ (2 : ℚ)), (∀ k, c ≤ n (k+1) / n k) →
    Summable (fun k => (1 : ℝ) / (Nat.fib <| n k))

theorem erdos_267.variants.specialization_pow_two :
    Irrational <| ∑' k, 1 / (Nat.fib <| 2^k)
```

`erdos_267.variants.two_le` is the formal-conjectures statement `erdos_267` with the hypothesis `c > 1` replaced by `c ≥ 2` (same conventions: `n : ℕ → ℕ`, ratio in `ℚ`, real `tsum`). `badea_criterion` proves that `∑ 1/a_k` is irrational (and summable) whenever `a_{k+1} > a_k² − a_k + 1` for all large `k`. Summability of every series is proved, so the `tsum`s are genuine sums.

## Proof outline

Badea's criterion: from `a_{k+1} − 1 > a_k(a_k − 1)` one gets `1/a_k + 1/(a_{k+1} − 1) < 1/(a_k − 1)`, and telescoping bounds the tails by `r_N < 1/(a_N − 1)`. If the sum were `p/q`, then `P_N = q·(∏_{k<N} a_k)·r_N` would be positive integers with `P_{N+1} < P_N`, which is impossible. For Fibonacci numbers, `F_{2m} > F_m² − F_m + 1` for `m ≥ 2` and `F` is monotone, so `n_{k+1} ≥ 2n_k` gives the growth condition.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos267.badea_criterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos267.erdos_267.variants.two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos267.erdos_267.variants.specialization_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos267.summable_of_two_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos267.summable_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos267.lean` (`55ba9e7280323adcc4005728de193cf38c8cd5163dba461ee79aba1b69a0d134`) are in `verification/`.

## Attribution

- Mathematics: C. Badea, *The irrationality of certain infinite series*, Glasgow Math. J. 29 (1987), 221–228 [Ba87]; C. Badea, *A theorem on irrationality of infinite series and applications*, Acta Arith. 63 (1993) [Ba93].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).
- Prior formal work: formal-conjectures records that the special case `erdos_267.variants.specialization_pow_two` (`∑ 1/F_{2^k}` irrational) already has a formal proof (mo271/formal-conjectures). It is included here only as a corollary and is not claimed as new; the new formalization is Badea's criterion and the `c ≥ 2` case.

No priority for the mathematics is claimed; the contribution is the Lean formalization.
