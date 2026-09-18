# PORTING-DIFF-127 — Erdos119.lean: mathlib v4.33.0 → v4.34.0

Pinned source: plby/lean-proofs @ `1268917de` `src/latest/ErdosProblems/Erdos119.lean`
(1788 lines; single-file closure, `import Mathlib` only)
Toolchain: Lean v4.34.0, mathlib v4.34.0 @ `5ed2965256430c3649e86755f9576b54eca72435`

The file was written for `leanprover/lean4:v4.33.0` / mathlib `v4.33.0`.
Only **two** minimal edits were needed for v4.34.0; all other 1780+ lines
(including every EReal / Real.rpow / Filter.limsup usage) elaborate unchanged.

## Fix 1 — `Finset.prod_le_prod` → `Finset.prod_le_prod₀` (line 58)
Old (two-explicit-argument form):
```
          apply Finset.prod_le_prod
          · exact fun i hi => norm_nonneg _
          · intro i hi ...
```
New:
```
          apply Finset.prod_le_prod₀
```
Why: in mathlib v4.34.0 `Finset.prod_le_prod` became the single-hypothesis
`[MulLeftMono]` variant; the two-argument (nonneg + pointwise) form was
renamed to `Finset.prod_le_prod₀`. (Same drift as JSP-000106
Discriminant.lean / PointCount.lean.)

## Fix 2 — drop obsolete rewrite in `cube_le_six_choose` (lines 776–777)
Old:
```
      norm_num [Nat.descFactorial_succ]
      have hsub : m + 3 - 2 = m + 1 := by omega
      rw [hsub]
      nlinarith
```
New:
```
      norm_num [Nat.descFactorial_succ]
      nlinarith
```
Why: in v4.34.0, after `norm_num [Nat.descFactorial_succ]` the goal is already
`m ^ 3 ≤ (m + 1) * ((m + 2) * (m + 3))` — the `m + 3 - 2` subterm is
normalized away, so `rw [hsub]` has no pattern to rewrite (`Tactic rewrite
failed: Did not find an occurrence of the pattern m + 3 - 2`). `nlinarith`
closes the goal directly.

## Axiom audit (expected, matches the file's own trailing comment block)
`Erdos119.erdos_119`, `.parts.i`, `.parts.ii`, `.parts.iii_quantitative`:
exactly `[propext, Classical.choice, Quot.sound]` — no sorryAx.
