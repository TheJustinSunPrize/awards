# JSP-000454: Erdős 564, the Erdős–Hajnal–Rado lower bound R_3(n) > 2^(cn²)

Catalog entry: [JSP-000454](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000454) · Problem source: [erdosproblems.com/564](https://www.erdosproblems.com/564)

## Problem

Let `R_3(n)` be the least `m` such that every 2-colouring of the 3-subsets of an `m`-set has a monochromatic `n`-set. Is there `c > 0` with `R_3(n) ≥ 2^{2^{cn}}`?

## Scope

Partial progress: the Erdős–Hajnal–Rado lower bound `R_3(n) > 2^{⌊n²/12⌋}` for `n ≥ 6`, and `∃ c > 0, ∀ᶠ n, 2^{c n²} ≤ R_3(n)`, together with the finite hypergraph Ramsey theorem, which shows the `sInf` defining `R_r(n)` is over a nonempty set. The doubly exponential question is open and not claimed.

## Formal statements

All results are in `Erdos564.lean`. `hypergraphRamsey` is copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`, Apache-2.0).

```lean
theorem erdos_564_lower_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (c * (n : ℝ) ^ 2) ≤ hypergraphRamsey 3 n

theorem two_pow_sq_div_twelve_lt_hypergraphRamsey_three {n : ℕ} (hn : 6 ≤ n) :
    2 ^ (n ^ 2 / 12) < hypergraphRamsey 3 n

theorem hypergraphRamsey_set_nonempty (r n : ℕ) :
    { m | ∀ (c : Finset (Fin m) → Bool),
      ∃ (S : Finset (Fin m)), S.card = n ∧
        ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }.Nonempty

theorem lt_hypergraphRamsey_three_of_choose (m n : ℕ) (h : 2 * m.choose n < 2 ^ n.choose 3) :
    m < hypergraphRamsey 3 n
```

With the formal-conjectures definition `hypergraphRamsey`: the defining set is nonempty for all `r, n` (hypergraph Ramsey theorem, proved here); `2·C(m,n) < 2^{C(n,3)}` implies `m < hypergraphRamsey 3 n`; hence `2^{⌊n²/12⌋} < hypergraphRamsey 3 n` for `n ≥ 6`, and `∃ c > 0, ∀ᶠ n in atTop, 2^(c·n²) ≤ hypergraphRamsey 3 n` (with `c = 1/12`), in the shape of the formal-conjectures statement `erdos_564`.

## Proof outline

Counting: the number of colourings `Finset (Fin m) → Bool` in which a fixed `n`-set is monochromatic on its 3-subsets is `2·2^{(total) − C(n,3)}`. A union bound over the `C(m,n)` choices of the set shows that if `2·C(m,n) < 2^{C(n,3)}`, some colouring has no monochromatic `n`-set. Since the `sInf` is attained (nonempty set) and colourings restrict to smaller `m`, this gives `m < R_3(n)`. Arithmetic: `2·C(2^t, n) ≤ 2^{t n} < 2^{C(n,3)}` when `t·n < C(n,3)`. Nonemptiness uses an induction proof of the finite `r`-uniform Ramsey theorem.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos564.erdos_564_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos564.two_pow_sq_div_twelve_lt_hypergraphRamsey_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos564.hypergraphRamsey_set_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos564.lt_hypergraphRamsey_three_of_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos564.lean` (`7ba1b566b4acdf66052185866df97888e264e715cff650dc3b7edb48972bfb8e`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, A. Hajnal, R. Rado, *Partition relations for cardinal numbers*, Acta Math. Acad. Sci. Hungar. 16 (1965), 93–196 [EHR65]; finite hypergraph Ramsey theorem: F. P. Ramsey (1930).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
