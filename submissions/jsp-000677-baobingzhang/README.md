# JSP-000677: Erdős 821, Pillai's theorem that totient multiplicities are unbounded

Catalog entry: [JSP-000677](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000677) · Problem source: [erdosproblems.com/821](https://www.erdosproblems.com/821)

## Problem

Let `g(n)` count the number of solutions to `φ(m) = n`. Is it true that for every `ε > 0` there are infinitely many `n` with `g(n) > n^{1−ε}`?

## Scope

Partial progress: Pillai's theorem `limsup g(n) = ∞`, which is the formal-conjectures variant `erdos_821.variants.pillai`. Erdős's `g(n) > n^c` infinitely often (which needs sieve input), Lichtman's result and the main question are not formalized or claimed.

## Formal statements

All results are in `Erdos821.lean`. `g` and the statement of `erdos_821.variants.pillai` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/821.lean`, Apache-2.0).

```lean
theorem erdos_821.variants.pillai :
    atTop.limsup (fun n : ℕ ↦ (g n : EReal)) = ⊤

theorem finite_setOf_totient_eq (n : ℕ) : {m : ℕ | totient m = n}.Finite

theorem two_pow_card_le_g {R : Finset ℕ} (hR : ∀ q ∈ R, q.Prime)
    (hdiv : ∀ q ∈ R, ∀ q' ∈ R, ¬ q ∣ q' - 1) :
    2 ^ R.card ≤ g (totient ((∏ q ∈ R, (q - 1)) * ∏ q ∈ R, (q - 1)))

theorem frequently_le_g (K : ℕ) : ∃ᶠ n in atTop, K ≤ g n
```

`erdos_821.variants.pillai : atTop.limsup (fun n ↦ (g n : EReal)) = ⊤` is proved with its exact formal-conjectures name and statement. Along the way: each fibre `{m | φ(m) = n}` is finite (so `ncard` is a genuine count), and for any finite set `R` of primes with no `q ∣ q' − 1` inside `R`, `g(φ(A²)) ≥ 2^{|R|}` where `A = ∏_{q∈R}(q − 1)`.

## Proof outline

For `U ⊆ R` let `m_U = A·∏_{q∈R∖U}(q − 1)·∏_{q∈U} q`. Its prime factors are those of `A` together with `U`, which are disjoint, and Euler's product formula gives `φ(m_U) = φ(A²)` for every `U`. `U` is recovered from the prime factors, so the `2^{|R|}` values are distinct. Arbitrarily large admissible `R` exist by Dirichlet's theorem (choose each new prime `p > ∏R + 2` with `p ≡ −1 (mod ∏R)`). Finiteness of fibres: `p ∣ m` implies `p − 1 ∣ φ(m)`, which bounds `m`. Unboundedness then gives `limsup = ⊤` in `EReal`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos821.erdos_821.variants.pillai' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos821.finite_setOf_totient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos821.two_pow_card_le_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos821.frequently_le_g' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos821.lean` (`8f4fa16cd7e766aab50db0ad67fe973e25cd0fdbe613788225d4885c605856d1`) are in `verification/`.

## Attribution

- Mathematics: S. S. Pillai, *On some functions connected with φ(n)*, Bull. Amer. Math. Soc. 35 (1929), 832–836 (unbounded multiplicities of totient values), as recorded in formal-conjectures and on erdosproblems.com/821; problem from P. Erdős [Er35b].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
