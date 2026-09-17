# JSP-000778: Erdős 936 conditional on abc: 2ⁿ ± 1 and n! ± 1 are powerful for only finitely many n (Cushing–Pascoe, CrowdMath)

Catalog entry: [JSP-000778](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000778) · Problem source: [erdosproblems.com/936](https://www.erdosproblems.com/936)

## Problem

Are `2ⁿ ± 1` and `n! ± 1` powerful (i.e. if `p ∣ m` then `p² ∣ m`) for only finitely many `n`?

## Scope

Partial progress: the conditional answers credited in the catalog record JSP-000778 — assuming the abc conjecture (an explicit hypothesis, never an axiom), each of `2ⁿ + 1`, `2ⁿ − 1`, `n! + 1`, `n! − 1` is powerful for only finitely many `n` (CrowdMath 2020 for `2ⁿ ± 1`; Cushing–Pascoe 2016 for `n! ± 1`). The unconditional questions remain open and are not claimed; the more general statements of the sources (`|x − n!| ≤ k`, `kⁿ + r`) are not formalized.

## Formal statements

All results are in `Erdos936.lean`. `Nat.Full`, `Nat.Powerful` (FormalConjecturesForMathlib/Data/Nat/Full.lean), `EventuallyNotPowerful` (FormalConjectures/ErdosProblems/936.lean) and `ABC.radical` (FormalConjectures/Wikipedia/ABC.lean) are copied verbatim from Google DeepMind's formal-conjectures project (Apache-2.0); `ABCConjecture` is the statement of formal-conjectures' `ABC.abc` with the binder `(hε : 0 < ε)` written as `0 < ε →` (the same proposition). It is used only as a hypothesis.

```lean
theorem erdos_936_of_abc (habc : ABCConjecture) :
    {n : ℕ | (2 ^ n + 1).Powerful}.Finite ∧ {n : ℕ | (2 ^ n - 1).Powerful}.Finite ∧
      {n : ℕ | (n ! + 1).Powerful}.Finite ∧ {n : ℕ | ((n)! - 1).Powerful}.Finite

theorem erdos_936.variants.two_pow_add_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (2 ^ · + 1)

theorem erdos_936.variants.two_pow_sub_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (2 ^ · - 1)

theorem erdos_936.variants.factorial_add_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (·! + 1)

theorem erdos_936.variants.factorial_sub_one_of_abc (habc : ABCConjecture) :
    EventuallyNotPowerful (·! - 1)

theorem eventuallyNotPowerful_iff_finite (a : ℕ → ℕ) :
    EventuallyNotPowerful a ↔ {n | (a n).Powerful}.Finite
```

With formal-conjectures' `Nat.Full`, `Nat.Powerful`, `EventuallyNotPowerful` (verbatim) and the abc conjecture `ABCConjecture` (formal-conjectures' `ABC.abc` statement as a `Prop`, `ABC.radical` verbatim): `erdos_936.variants.{two_pow_add_one, two_pow_sub_one, factorial_add_one, factorial_sub_one}_of_abc : ABCConjecture → EventuallyNotPowerful (…)`, which are the right-hand sides of formal-conjectures' four open variants (answer 'yes' under abc), `eventuallyNotPowerful_iff_finite`, and the combined `erdos_936_of_abc : ABCConjecture → {n | Powerful (2ⁿ+1)}.Finite ∧ {n | Powerful (2ⁿ−1)}.Finite ∧ {n | Powerful (n!+1)}.Finite ∧ {n | Powerful (n!−1)}.Finite`.

## Proof outline

A nonzero powerful `x` has `rad(x)² ≤ x`. With `rad(ab) ≤ rad(a)rad(b)`, `rad(2ⁿ) = 2` and `rad(n!) ∣ primorial(n) ≤ 4ⁿ`, apply abc with `ε = 1/3` to coprime triples `(a, 1, a+1)`: only finitely many `a > 0` have `rad(a(a+1))⁴ < (a+1)³`. For `a ∈ {2ⁿ, 2ⁿ − 1, n!, n! − 1}` with the neighbour powerful, `rad(a(a+1)) ≤ R·√(a+1)` with `R = 2` or `4ⁿ`, and `R⁴ < a + 1` holds for all large `n` (`256ⁿ < n!` eventually), so each such `n` gives a distinct exceptional triple; hence finitely many `n`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos936.erdos_936_of_abc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos936.erdos_936.variants.two_pow_add_one_of_abc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos936.erdos_936.variants.two_pow_sub_one_of_abc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos936.erdos_936.variants.factorial_add_one_of_abc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos936.erdos_936.variants.factorial_sub_one_of_abc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos936.eventuallyNotPowerful_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos936.lean` (`e839fbf6a7d0972791a943c8eb7595bb68d889527a8eb5beb989c66f3fac79f3`) are in `verification/`.

## Attribution

- Mathematics: CrowdMath, *Applications of the abc conjecture to powerful numbers*, arXiv:2005.07321 (2020) [Cr20] (`2ⁿ ± 1`), and C. Cushing, J. Pascoe, *Powerful numbers and the ABC-conjecture*, arXiv:1611.01192 (2016) [CuPa16] (`n! ± 1`), both cited by the catalog record JSP-000778 and erdosproblems.com/936; problem of Erdős [Er76d, p. 32]. The Lean proof uses the standard radical estimates, not a line-by-line transcription of the sources.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
