# JSP-000055: Erdős 18, Erdős's bound h(n!) < n

Catalog entry: [JSP-000055](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000055) · Problem source: [erdosproblems.com/18](https://www.erdosproblems.com/18)

## Problem

A number `m` is *practical* if every `1 ≤ t < m` is a sum of distinct divisors of `m`; `h(m)` is the number of divisors that always suffice. Erdős asked whether infinitely many practical `m` have `h(m) < (log log m)^{O(1)}`, and whether `h(n!) < n^{o(1)}`, or even `h(n!) < (log n)^{O(1)}`.

## Scope

Partial progress: Erdős's bound `h(n!) < n` (for all `n ≥ 2`), recorded on erdosproblems.com/18. The open questions (`h(n!) < n^{o(1)}`, `(log n)^{O(1)}`, the `log log` question) and Vose's theorem are not addressed.

## Formal statements

All results are in `Erdos18.lean`. `practicalH` and `subsetSums` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/18.lean` and `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`, Apache-2.0).

```lean
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n

theorem practicalH_factorial_le {n : ℕ} (hn : 2 ≤ n) : practicalH n.factorial ≤ n - 1

theorem exists_divisors_sum_of_lt_factorial {n : ℕ} (hn : 1 ≤ n) :
    ∀ m < n.factorial, ∃ S : Finset ℕ, S ⊆ n.factorial.divisors ∧ S.card ≤ n - 1 ∧
      m = ∑ i ∈ S, i
```

`erdos_18_upper_bound` has the exact name and statement of the formal-conjectures theorem (category "research solved"), which is stated with `sorry` upstream. It is proved here, in the quantitative form `h(n!) ≤ n - 1` for all `n ≥ 2`.

## Proof outline

Induction on `n`: every `m < n!` is a sum of a set of at most `n - 1` distinct divisors of `n!`. For the step, write `m = (n+1)·q + r` with `q < n!` and `0 ≤ r ≤ n`. Scale the divisor set representing `q` by `n + 1`; these are divisors of `(n+1)!`, all `≥ n + 1`. Then add `r` (a divisor of `(n+1)!`, distinct from the scaled ones because `r < n + 1`) when `r ≠ 0`. The value `m = n!` itself is the single divisor `n!`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos18.erdos_18_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos18.practicalH_factorial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos18.lean` (`6336df3b72a1d88675c87f180a64382dd030b612434ed7fb94db3740fde68ba9`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős (`h(n!) < n`), as recorded on erdosproblems.com/18; see also M. Vose, *Egyptian fractions*, Bull. London Math. Soc. 17 (1985), 21–24 [Vo85].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
