# PORTING DIFF — JSP-000106 (Erdos #183-counterexample, "Alpoge unit distance")

Target: upstream `plby/lean-proofs @ 1268917de`, Erdos90b closure (ErdosUnitDistance 9 + TauCeti 12 + vendored PrimeNumberTheoremAnd 9).
Base toolchain: Lean v4.34.0, mathlib v4.34.0 (5ed2965256430c3649e86755f9576b54eca72435), source-built, `MATHLIB_CACHE_DISABLE=1`.
LEAN_PATH: glob of all `work\jsp-071\verify-current\.lake\packages\*` + `$base\.lake\build\lib\lean` + `$base\olean` (10 package entries; handwritten subsets fail on `unknown module prefix 'ImportGraph'`).

## Patching done (byte-level vs pinned upstream)

| File | Line(s) | Upstream (1268917de) | Patched | Reason |
|---|---|---|---|---|
| `PrimeNumberTheoremAnd/Sobolev.lean` | 308–309 | `· congr 1` + `· ring` | `· ring_nf` | mathlib 4.34 ordered-group/semiring norm synthesis stricter; `congr 1` left unsolved goal; `ring_nf` closes both (independently verified: standalone compile exit 0, 14.6 s warm) |
| `PrimeNumberTheoremAnd/Wiener.lean` | 2827 | `(fun σ' ↦` | `(fun (σ' : ℝ) ↦` | Elaboration-order bug under Lean 4.34: in the `haux` `EventuallyEq` statement the left lambda's binder was unpinned, so when `x ^ (1 - σ')` triggered `HPow ℝ ?m` typeclass search the exponent type was still an open metavariable and search was ambiguous among the ℕ / ℤ / ℝ instances (`failed to synthesize HPow ℝ ℝ ?m.380`). Ascribing the binder pins `σ' : ℝ` before the body elaborates; `HPow ℝ ℝ` (real-exponent `^` = `Real.rpow`, which mathlib 4.34 does provide, cf. `Analysis/SpecialFunctions/Pow/Asymptotics.lean`) then resolves uniquely. The two sibling `let`s (`Pole`, `RHS`) already pin σ' via their type ascriptions and were unaffected. |
| `PrimeNumberTheoremAnd/Consequences.lean` | ~131 (isLittleO_sqrt_mul_log) | `· rfl` | `· rw [← sqrt_eq_rpow, div_sqrt, sqrt_eq_rpow]`; dropped 2 extra `convert` bullets | In mathlib 4.34 `Real.sqrt` is no longer definitionally `x ^ (1/2)` (`Real.sqrt_eq_rpow` is a theorem), so the pointwise subgoal `x / √x = x ^ (1/2)` needs the same rewrite chain already used one bullet below; `convert` also produces one subgoal fewer here, so the trailing `rfl`/`rw` bullets were removed ("No goals to be solved"). |
| `PrimeNumberTheoremAnd/Consequences.lean` | ~171 (chebyshev_asymptotic) | `· rfl` + 2 trailing bullets | `· ext x; ring` + drop 2 extra `convert` bullets | `convert ... using 1` in 4.34 leaves `(fun x ↦ 2 * √x * log x) = (fun x ↦ 2 * (√x * log x))` (ℝ-mult assoc, never defeq) as the first subgoal; `ext x; ring` closes it. The second subgoal (`rfl`) is retained; the two extra bullets from the upstream mathlib's subgoal layout are removed. |
| `PrimeNumberTheoremAnd/Consequences.lean` | ~897 (nth_prime_asymp) | trailing `· ext n; simp only [Pi.mul_apply]` bullet | removed | `convert ... using 1` produces only one subgoal in 4.34 (closed by `field`); the extra bullet is gone. |
| `PrimeNumberTheoremAnd/Consequences.lean` | ~1854 (lambda_eq_sum_sq_dvd_mu) | ends `norm_num +zetaDelta` | append `congr 1; apply Finset.sum_congr rfl; intro p hp; exact Nat.primeFactorsList_count_eq` | 4.34 leaves `(-1) ^ (∑ a ∈ n.primeFactors, n.primeFactorsList.count a) = (-1) ^ (∑ p ∈ n.primeFactors, n.factorization p)`; closed by congruence on the exponents (per-element identity `Nat.primeFactorsList_count_eq`). |
| `ErdosProblems/Erdos90b/External/ErdosUnitDistance/MultiquadraticField.lean` | 41 | `exact Complex.isIntegral_rat_I` | `exact Complex.isIntegral_I ℚ` | mathlib 4.34 deprecated `Complex.isIntegral_rat_I` and generalized it to `Complex.isIntegral_I (R) [CommRing R] [Algebra R ℂ] : IsIntegral R Complex.I` with an *explicit* first argument; `ℚ` must be supplied (bare application now mismatches). |
| `ErdosProblems/Erdos90b/External/TauCeti/NumberTheory/EffectiveBounds/IdealCount/Basic.lean` | header | (none) | `+ public import Mathlib.Algebra.CharZero.Infinite` | mathlib 4.34's `Ideal.absNorm` is declared `[IsDedekindDomain S] [Infinite S]` (typeclass API change vs the mathlib TauCeti was written against). `Infinite (𝓞 F)` would resolve via `CharZero.infinite` (`[CharZero M] → Infinite M`, `Mathlib/Algebra/CharZero/Infinite.lean`) but that module is not transitively imported by the TauCeti closure (verified: instance absent from `synthInstance` candidate list; `CharZero (𝓞 F)` itself synthesizes fine via `NumberField.Basic`). Added the import to the 4 files that call `Ideal.absNorm` directly. Verified: standalone `IdealCount/Basic.lean` compile exit 0 (2 deprecation warnings only, no errors). |
| `ErdosProblems/Erdos90b/External/ErdosUnitDistance/NormFibre.lean` | header | (none) | `+ import Mathlib.Algebra.CharZero.Infinite` | Same `[Infinite S]` requirement; EUD file uses `Ideal.absNorm` directly (19 refs). |
| `ErdosProblems/Erdos90b/External/ErdosUnitDistance/PointCount.lean` | header | (none) | `+ import Mathlib.Algebra.CharZero.Infinite` | Same `[Infinite S]` requirement; EUD file uses `Ideal.absNorm` directly (11 refs). |
| `ErdosProblems/Erdos90b/External/ErdosUnitDistance/Discriminant.lean` | 296, 314 (+ comment at 286) | `Finset.prod_le_prod` (two-arg nonneg/le form) | `Finset.prod_le_prod₀` | mathlib 4.34 renamed/dropped the two-argument `Finset.prod_le_prod` in favor of the `₀` (nonneg) variant (same family as the 147-side `BinaryEntropy` fix); both inequality cites are `∀ i, 0 ≤ f i`-style, so the `₀` form closes them outright. Verified: standalone compile exit 0 (21 s warm). |
| `ErdosProblems/Erdos90b/External/ErdosUnitDistance/PointCount.lean` | 153 | `Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun w _ => h_prod_le w` (two-arg form, nonneg first) | `Finset.prod_le_prod₀` | In 4.34 `Finset.prod_le_prod` is now the single-argument `[MulLeftMono]` variant (inapplicable to ℝ); the two-arg nonneg form lives only as `prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i)` — argument order matches the call as written, rename alone suffices. Verified: standalone compile exit 0 (525 s). |

(ClassNumber/Basic.lean also uses `Ideal.absNorm` but is covered transitively via its `public import ... IdealCount.Basic` module re-export.)

No other source-level changes. All 30 non-entry modules otherwise byte-identical to pinned upstream; `Erdos90b.lean` entry + `Audit90b.lean` are ours (verification-only wrapper, not math content).

## Infra fixes (not porting, recorded for transparency)

- `compile106.ps1` previously did not pre-create lean output dirs for TauCeti deep namespaces
  (`External/TauCeti/LinearAlgebra/Dimension`, `External/TauCeti/FieldTheory[/IntermediateField]`,
  `External/TauCeti/NumberTheory/DedekindDomain`), producing `lean.exe: failed to write ... .olean: failed to create file`
  fake exit=1s. Fixed by adding the missing `New-Item` blocks plus a defensive auto-mkdir loop over all 32 step
  output dirs (derived from `Split-Path` of each `-o` target).

## Notes for the record

- `PrimeNumberTheoremAnd` is vendored inside the pinned repo (local package), transitively importing mathlib
  `NumberTheory.LSeries.PrimesInAP`, `Harmonic`, `Chebyshev` — all present in mathlib v4.34.0; no BoundedGaps /
  alexKontorovich modules needed.
- TauCeti modules use Lean-2026-style `module` / `public import` syntax — verified compatible with v4.34.0.
- Axiom audit expected: `[propext, Classical.choice, Quot.sound]` plus anything pulled in by the analytic PNT
  machinery (recorded honestly in `verification/record.yaml`); the theorem itself is the counterexample bound
  `Erdos90b.not_erdos_90` (all `n^(1+C/log log n)` distance-bounds fail for the explicit family).
