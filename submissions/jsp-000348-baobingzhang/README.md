# JSP-000348: Erdős 423, Bolan–Tang 2026: the Hofstadter consecutive-sum sequence omits infinitely many integers, with a_n − n ≫ log log n

Catalog entry: [JSP-000348](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000348) · Problem source: [erdosproblems.com/423](https://www.erdosproblems.com/423)

## Problem

Let `a₁ = 1`, `a₂ = 2`, and for `k ≥ 3` let `a_k` be the least integer `> a_{k−1}` which is the sum of at least two consecutive terms of the sequence (OEIS A005243). What is the asymptotic behaviour of this sequence?

## Scope

Partial progress: the 2026 results of Bolan and Tang that `a_n − n` is nondecreasing and unbounded (so infinitely many positive integers are omitted), and Tang's lower bound `a_n − n = Ω(log log n)`, i.e. the formal-conjectures variants `erdos_423.variants.unbounded`, `infinite_complement`, `lower_bound` (and `nondecreasing`). The asymptotic behaviour asked by Erdős (conjecturally `a_n = n + o(n)`), Tang's upper bound `a_n ≪ n^{1/(c−1)+o(1)}` (formal-conjectures `upper_bound`) and the main statement `erdos_423` are not formalized or claimed.

## Formal statements

All results are in `Erdos423.lean`. `IsConsecutiveBlockSum`, `IsHofstadterSeq` and the statements of `erdos_423.variants.nondecreasing`, `unbounded`, `infinite_complement`, `lower_bound` and `erdos_423.test.unbounded_iff_infinite_complement` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/423.lean`, Apache-2.0). The value `a 0` is unconstrained by `IsHofstadterSeq`; this changes `Set.range a` by at most one element and does not affect the results.

```lean
theorem erdos_423.variants.unbounded :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n

theorem erdos_423.variants.infinite_complement :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ

theorem erdos_423.variants.lower_bound :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    (fun n : ℕ => Real.log (Real.log n)) =O[atTop]
      (fun n : ℕ => (a n : ℝ) - n)

theorem erdos_423.variants.nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m

theorem exists_isHofstadterSeq : ∃ a : ℕ → ℕ, IsHofstadterSeq a

theorem eq_of_isHofstadterSeq {a b : ℕ → ℕ} (ha : IsHofstadterSeq a) (hb : IsHofstadterSeq b) :
    ∀ n, 1 ≤ n → a n = b n

theorem plateau_bound (h : IsHofstadterSeq a) {n1 n2 B : ℕ} (hn1 : 1 ≤ n1)
    (ha1 : a n1 = B + n1) (ha2 : a n2 = B + n2) :
    B + n2 < 512 * ((B + n1) * (B + n1) * ((B + n1) * (B + n1)))

theorem lt_of_le_add (h : IsHofstadterSeq a) (B : ℕ) :
    ∀ n, 1 ≤ n → a n ≤ B + n → n < 2 ^ 2 ^ (3 * B + 4)
```

With the formal-conjectures definitions `IsConsecutiveBlockSum` and `IsHofstadterSeq` (verbatim), the file proves `erdos_423.variants.nondecreasing`, `erdos_423.variants.unbounded : ∀ a, IsHofstadterSeq a → ∀ M, ∀ᶠ n in atTop, M + n ≤ a n`, `erdos_423.variants.infinite_complement : ∀ a, IsHofstadterSeq a → (Set.range a)ᶜ.Infinite` and `erdos_423.variants.lower_bound : ∀ a, IsHofstadterSeq a → (fun n => log (log n)) =O[atTop] (fun n => (a n : ℝ) − n)`, all with their exact formal-conjectures names and statements. It also proves that the definition is satisfiable (`exists_isHofstadterSeq`, by an explicit recursive construction) and determines the sequence uniquely for `n ≥ 1` (`Hofstadter.eq_of_isHofstadterSeq`), so the statements are not vacuous. The explicit bound proved is: `a n ≤ B + n` implies `n < 2^(2^(3B+4))` (`Hofstadter.lt_of_le_add`).

## Proof outline

Since `a` is strictly increasing, `b_n = a_n − n` is nondecreasing. On a plateau `b = B` on `[n₁, n₂]` (so `a_l = T + (l − n₁)` with `T = B + n₁`), a power of two `2^r > T²` in the plateau range cannot be a sum of ≥ 2 consecutive terms inside the plateau (a power of two is not a sum of ≥ 2 consecutive integers), so it is `C + (T + s) + … + (T + v)` with a bounded prefix contribution `C ≤ T²`; completing the square gives `x² + 8C + 4T = 8·2^r + 4T² + 1` with `x` odd (`Hofstadter.plateau_rep`). Comparing the representations of `2^r` and `2^{r+2}` gives `4x² + 32C + 12T = y² + 8C' + 12T² + 3` with `y` odd, hence `y ≠ 2x` and `|y² − 4x²| ≥ 2x`, forcing `x ≤ 16T²`, which is impossible once `2^r > 64T⁴`. So every plateau ends before `512·T⁴` (`Hofstadter.plateau_bound`), and induction on `B` gives `n < 2^(2^(3B+4))` whenever `a_n ≤ B + n`. This yields unboundedness, the `Ω(log log n)` lower bound, and (by counting) infinitely many omitted integers. Tang closes the plateau step with the Schinzel–Tijdeman and Beukers theorems and Bolan uses a pigeonhole argument; the elementary comparison of `2^r` with `2^{r+2}` used here replaces those inputs (it was found during the AI-assisted formalization) and gives the recursion `M(B) ≪ M(B−1)^4`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos423.erdos_423.variants.unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.erdos_423.variants.infinite_complement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.erdos_423.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.erdos_423.variants.nondecreasing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.exists_isHofstadterSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.Hofstadter.eq_of_isHofstadterSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.Hofstadter.plateau_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos423.Hofstadter.lt_of_le_add' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos423.lean` (`0127d69c795b50dce2c65841e1ed42e6a0fe1a6f91502d40aa868423816043dc`) are in `verification/`.

## Attribution

- Mathematics: Q. Tang, *The Hofstadter consecutive-sum sequence omits infinitely many positive integers*, arXiv:2603.09939 (March 2026) [Ta26], and M. Bolan, *Hofstader–Ulam Sequence* (January 2026, github.com/mjtb49/HofstaderUlam), who independently proved that `a_n − n` is unbounded; both are cited by the catalog record JSP-000348 and erdosproblems.com/423. Problem of Hofstadter, from P. Erdős [Er77c] and Erdős–Graham [ErGr80].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
