# JSP-000227: Erdős 263, Koizumi's theorem: ⌊α^(2^n)⌋ is an irrationality sequence for all but countably many α > 1

Catalog entry: [JSP-000227](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000227) · Problem source: [erdosproblems.com/263](https://www.erdosproblems.com/263)

## Problem

A sequence `a_n` of positive integers is an irrationality sequence (in the sense used here) if `∑ 1/b_n` is irrational for every sequence of positive integers `b_n` with `a_n/b_n → 1`. Is `a_n = 2^{2^n}` an irrationality sequence? Must every irrationality sequence satisfy `a_n^{1/n} → ∞`?

## Scope

Partial progress: Koizumi's result (arXiv:2504.05933, Theorem 4), credited in the catalog record JSP-000227, that `⌊α^{2^n}⌋` is an irrationality sequence for all `α > 1` outside a countable set, i.e. the formal-conjectures variant `erdos_263.variants.doubly_exponential_all_but_countable`. The two questions of Erdős Problem 263 (whether `2^{2^n}` itself is an irrationality sequence, and the growth question), Koizumi's explicit Theorem 1 and his corollaries, and the Google DeepMind counterexample also credited in the record are not formalized or claimed here.

## Formal statements

All results are in `Erdos263.lean`. `IsWeakIrrationalitySequence` and the statement of `erdos_263.variants.doubly_exponential_all_but_countable` are copied verbatim, with docstrings, from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/263.lean`, Apache-2.0). Sequences are indexed from `n = 0`, which is equivalent to Koizumi's `n ≥ 1` convention (one term does not affect irrationality).

```lean
theorem erdos_263.variants.doubly_exponential_all_but_countable :
    ∀ᶠ (α : ℝ) in .cocountable, α > 1 →
      IsWeakIrrationalitySequence (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊)
```

`erdos_263.variants.doubly_exponential_all_but_countable : ∀ᶠ (α : ℝ) in .cocountable, α > 1 → IsWeakIrrationalitySequence (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊)` is proved with its exact formal-conjectures name, statement and definition of `IsWeakIrrationalitySequence` (positive, monotone, and `∑' 1/b_n` irrational for every positive `b` with `a_n/b_n → 1`). The proof establishes summability of every admissible `∑ 1/b_n` before using its value, so Lean's convention that a non-summable `tsum` is `0` plays no role.

## Proof outline

Suppose `α > 1` and some positive `b` with `⌊α^{2^n}⌋/b_n → 1` has `∑ 1/b_n = q ∈ ℚ`. Then `b_n → ∞` and `b_n²/b_{n+1} → 1`, so eventually `b_{n+1} ≥ 2b_n`; the series is summable and the tails satisfy `t_n ≤ 2/b_n`. From `t_n = 1/b_n + t_{n+1}` one gets `b_n t_n → 1`, `b_n² t_{n+1} → 1` and hence `(t_n)⁻¹ + 1 − b_n → 0` (Koizumi's Theorem 1 with `β = 1` in limit form). Since `t_n = q − ∑_{k<n} 1/b_k`, from some `M` on `b_n` is the unique integer within `1/2` of `(q − ∑_{k<n} 1/b_k)⁻¹ + 1`, so `b` is determined by `M`, `q` and its first `M` terms: such sequences form a countable set. Finally `b` determines `α`, because `b_n/α^{2^n} → 1` and `b_n/β^{2^n} → 1` with `α < β` would force `(β/α)^{2^n} → 1`. Hence the exceptional `α` lie in a countable union of subsingletons.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos263.erdos_263.variants.doubly_exponential_all_but_countable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos263.lean` (`935bad8a7d6b5e1802adc522bfe02513a7d692d61a2b7b6465b7f30027dd1b66`) are in `verification/`.

## Attribution

- Mathematics: J. Koizumi, *Irrationality of the reciprocal sum of doubly exponential sequences*, arXiv:2504.05933 (2025) [Ko25c], Theorem 4, cited by the catalog record JSP-000227 and erdosproblems.com/263. Problem of Erdős and Graham [ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
