# JSP-000128 / Erdős 120: the finite-set variant

This standalone Lean package proves the known finite-set variant of Erdős's similarity problem: every measurable subset of the real line with positive Lebesgue measure contains an affine copy of every finite set. The scale is proved to be positive, and hence nonzero. The formal measurability hypothesis is `MeasurableSet E`, exactly as in the public target.

The mathematical result is commonly attributed to Hugo Steinhaus (1920). This is a formalization of known mathematics. **It does not solve the conjecture about infinite sets.**

## Theorems and exact scope

- `compact_finite_pattern`: every compact set of positive measure contains a positively scaled and translated copy of each finite real pattern.
- `finite_pattern`: the same conclusion for every measurable set of positive measure, including sets of infinite measure and the empty finite pattern.
- `finite_set`: the exact `erdos_120.variants.finite_set` target from the pinned Formal Conjectures source, using its `Erdos120For` definition.
- `Audit.exact_statement`: repeats the public definition independently and checks the target against it by definitional equality.
- `Audit.affine_copy`: spells out the nonzero scale, translation, and membership quantifiers directly.

The proof takes a compact subset of positive measure. For each pattern point `x`, translation by `t*x` loses measure tending to zero as `t` tends to zero. A finite sum of these losses is smaller than the compact set's measure for some positive `t`. Translation invariance and the finite union bound then leave a translation that places all pattern points inside the compact set. The argument uses mathlib's existing translation-continuity and inner-regularity theorems.

## Reproduce

Install the toolchain in `lean-toolchain`, then run here:

```sh
lake exe cache get Mathlib.MeasureTheory.Measure.Haar.Basic Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.Tactic.Push
bash tools/verify.sh
```

The dependencies are pinned in `lake-manifest.json`. The verification script builds both modules, checks the statement and transitive axioms, and replays the complete imported environment with bundled `leanchecker --fresh`. This replay uses Lean's own kernel; it is not an independent verifier implementation. See `verification/RESULTS.md` for the recorded checks.

## Sources and attribution

- [Exact Formal Conjectures source and finite-set variant](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/120.lean), Apache-2.0.
- [Erdős Problems 120](https://www.erdosproblems.com/120).
- Hugo Steinhaus, *Sur les distances des points dans les ensembles de mesure positive*, Fundamenta Mathematicae 1 (1920), 93–104, [original paper](https://matwbn.icm.edu.pl/ksiazki/fm/fm1/fm1111.pdf).
- Yeonwook Jung, Chun-Kit Lai, and Yuveshen Mooroogen, [*Fifty years of the Erdős similarity conjecture*, §1](https://arxiv.org/html/2412.11062v2#S1), which records finite-set measure universality and its attribution to Steinhaus.
- [Pinned mathlib translation-continuity results](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Group/Measure.lean).

New proof formalization and packaging: GitHub account `James-16`, with substantial OpenAI Codex assistance. No conjecture-library placeholders are imported. The target definition and statement retain their original attribution; see `NOTICE`.

This package makes no claim of exhaustive priority, prize eligibility, recipient confirmation, or an award. Those decisions remain with the organizers.
