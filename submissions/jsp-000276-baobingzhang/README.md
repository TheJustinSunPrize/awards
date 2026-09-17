# JSP-000276: Erdős 332, positive (upper Banach) density forces D(A) to have bounded gaps

Catalog entry: [JSP-000276](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000276) · Problem source: [erdosproblems.com/332](https://www.erdosproblems.com/332)

## Problem

Let `A ⊆ ℕ` and let `D(A)` be the set of integers that occur infinitely often as `a₁ − a₂` with `a₁, a₂ ∈ A`. What conditions on `A` are sufficient to ensure that `D(A)` has bounded gaps?

## Scope

Partial progress: the problem is open-ended. This formalizes the sufficient condition recorded on erdosproblems.com/332 (positive density, Prikry–Tijdeman–Stewart) together with the strengthening to positive upper density and to positive upper Banach density (observed on the erdosproblems forum in May 2026). No characterisation of sufficient conditions, nothing about sets of zero upper Banach density, and none of the related questions (positive density of `D(A)`, divergence of `∑ 1/d`, `D(A) ≠ ∅`) are claimed.

## Formal statements

All results are in `Erdos332.lean`. `D_A` and `HasBoundedGaps` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/332.lean`), and `Set.partialDensity`, `Set.upperDensity`, `Set.HasDensity`, `Set.HasPosDensity` verbatim from `FormalConjecturesForMathlib/Data/Set/Density.lean` (Apache-2.0). `upperBanachDensity` is defined in the file in the standard way, `limsup_{L→∞} sup_M |A ∩ [M, M+L)| / L`.

```lean
theorem erdos_332.variants.upperBanachDensity_pos (A : Set ℕ) :
    0 < upperBanachDensity A → HasBoundedGaps (D_A A)

theorem erdos_332.variants.upperDensity_pos (A : Set ℕ) :
    0 < A.upperDensity → HasBoundedGaps (D_A A)

theorem erdos_332.variants.hasPosDensity (A : Set ℕ) :
    A.HasPosDensity → HasBoundedGaps (D_A A)

theorem upperDensity_le_upperBanachDensity (A : Set ℕ) :
    A.upperDensity ≤ upperBanachDensity A

theorem upperDensity_univ : (Set.univ : Set ℕ).upperDensity = 1
```

With the formal-conjectures definitions `D_A` and `HasBoundedGaps` (verbatim), the file proves `0 < upperBanachDensity A → HasBoundedGaps (D_A A)`, `0 < A.upperDensity → HasBoundedGaps (D_A A)` and `A.HasPosDensity → HasBoundedGaps (D_A A)`, i.e. the formal-conjectures statement `erdos_332` with its `answer(…)` placeholder instantiated by each of these conditions. It also proves `upperDensity ≤ upperBanachDensity` and that `ℕ` has upper density 1 (the hypotheses are satisfiable; the conclusion fails for `D(A) = ∅`).

## Proof outline

Call a finite `F ⊆ ℤ` separated if `s − t ∉ D(A)` for distinct `s, t ∈ F`. Only finitely many `a ∈ A` satisfy `a + s = b + t` with `b ∈ A`, `s ≠ t ∈ F`, so the translates of `A ∩ [M, M + L)` by elements of `F` are disjoint up to a bounded error inside an interval of length `L + 2T`; hence `|F| · |A ∩ [M, M + L)| ≤ L + 2T + |F|(K + 1)` and, letting `L → ∞`, `|F| · d*(A) ≤ 1`. So separated sets have at most `1/d*(A)` elements and `A` is infinite (so `0 ∈ D(A)`). For a separated `F` of maximal size and `R = max |f|`, every `w = z + R` has `w − f ∈ D(A)` for some `f ∈ F`, and `z ≤ w − f < z + 2R + 1`, so `D(A)` meets every window of length `2R + 1`. Upper density is at most upper Banach density, and positive natural density gives positive upper density.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos332.erdos_332.variants.upperBanachDensity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos332.erdos_332.variants.upperDensity_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos332.erdos_332.variants.hasPosDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos332.upperDensity_le_upperBanachDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos332.upperDensity_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos332.lean` (`ed4ee343499fc1f63689c11f0a276161806b967d8096308dcd3ab5fb9daa465d`) are in `verification/`.

## Attribution

- Mathematics: Sufficient condition of positive density: K. Prikry, R. Tijdeman, C. L. Stewart and others, see C. L. Stewart, *On difference sets of sets of integers*, Séminaire Delange-Pisot-Poitou 1977/78 [St78] and R. Tijdeman, *Distance sets of sequences of integers* (1979) [Ti79], as cited by the catalog record JSP-000276 and erdosproblems.com/332. Upper Banach density strengthening: forum comment on erdosproblems.com/forum/thread/332 by user "aditya" (4 May 2026), introduced as an observation by GPT-5.5 Pro. Problem from Erdős–Graham [ErGr80, p. 50].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
