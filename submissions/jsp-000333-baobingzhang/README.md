# JSP-000333: Erdős 406, Narkiewicz's bound on powers of 2 with ternary digits 0 and 1

Catalog entry: [JSP-000333](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000333) · Problem source: [erdosproblems.com/406](https://www.erdosproblems.com/406)

## Problem

Is it true that there are only finitely many powers of `2` which have only the digits `0` and `1` when written in base `3`?

## Scope

Partial progress: Narkiewicz's upper bound `N(x) ≪ x^{log 2 / log 3}` for the number of `n ≤ x` such that `2^n` has only ternary digits `0` and `1`, with an explicit constant. Finiteness (the problem itself) is open and not claimed.

## Formal statements

All results are in `Erdos406.lean`. The digit condition `Nat.digits 3 m ⊆ [0, 1]` is copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/406.lean`, Apache-2.0); as in Narkiewicz, the count is indexed by the exponent `n` (with `n = 0` counted).

```lean
theorem erdos_406_narkiewicz (x : ℝ) (hx : 1 ≤ x) :
    ({n : ℕ | (n : ℝ) ≤ x ∧ Nat.digits 3 (2 ^ n) ⊆ [0, 1]}.ncard : ℝ) ≤
      2 ^ (1 - Real.log 2 / Real.log 3) * x ^ (Real.log 2 / Real.log 3)

theorem erdos_406_isBigO :
    (fun x : ℝ => ({n : ℕ | (n : ℝ) ≤ x ∧ Nat.digits 3 (2 ^ n) ⊆ [0, 1]}.ncard : ℝ))
      =O[Filter.atTop] (fun x : ℝ => x ^ (Real.log 2 / Real.log 3))

theorem card_filter_range_le (j : ℕ) :
    ((Finset.range (2 * 3 ^ j)).filter (fun n => Nat.digits 3 (2 ^ n) ⊆ [0, 1])).card ≤ 2 ^ j
```

Explicit form of Narkiewicz's theorem: for every real `x ≥ 1`, `#{n ≤ x : Nat.digits 3 (2^n) ⊆ [0, 1]} ≤ 2^{1 - log 2/log 3} · x^{log 2/log 3}` (constant ≈ 1.29, attained at `x = 2`), together with the `=O[atTop]` form and the discrete bound `#{n < 2·3^j : …} ≤ 2^j`.

## Proof outline

(1) The multiplicative order of `2` modulo `3^{j+1}` is `2·3^j` (via `ZMod.orderOf_one_add_prime` for `4 = 1 + 3` and parity mod 3), so `n ↦ 2^n mod 3^{j+1}` is injective on `[0, 2·3^j)`. (2) If `2^n` has only ternary digits 0 and 1, its lowest digit is 1 (as `3 ∤ 2^n`) and its residue mod `3^{j+1}` is determined by `j` further digits in `{0, 1}`, so at most `2^j` residues occur. (3) Hence at most `2^j` such `n` below `2·3^j`, and choosing `j` minimal with `⌊x⌋ < 2·3^j` gives the real-exponent bound using `3^{log 2/log 3} = 2`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos406.erdos_406_narkiewicz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos406.erdos_406_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos406.card_filter_range_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos406.lean` (`2f467af405f31ff7686537a3f2da6ad41d09a629f785d49cab94d053a081501c`) are in `verification/`.

## Attribution

- Mathematics: W. Narkiewicz, *A note on a paper of H. Gupta concerning powers of two and three*, Univ. Beograd. Publ. Elektrotehn. Fak. Ser. Mat. Fiz. (1980), 173–174 [Na80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
