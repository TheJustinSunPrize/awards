/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000903 — Observation record: four planar points determining four
equal-area triangles (the unit-square witness, `n = 4` case).

Catalog question (TheJustinSunPrize/awards, problems/catalog-0901-1000.md,
#JSP-000903):
  "How many triangles of the same area can a finite planar point set
   determine?"

Scope of this file
------------------
A finite set of `n` planar points determines at most `n.choose 3`
triangles, one for each triple of distinct points.  This file records a
complete, machine-checked Lean proof of the `n = 4` attainment instance:
the four vertices of the unit square determine exactly the `C(4,3) = 4`
triples, and every one of them is a genuine triangle of the same
(absolute) area.  Concretely, for

    s = {(0,0), (1,0), (1,1), (0,1)} ⊂ ℚ²,

every ordered triple of pairwise distinct points `a b c ∈ s` satisfies
`|area2 a b c| = 1`, where `area2 a b c` is the doubled signed area of
the triangle `abc`:

    area2 a b c = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x).

Thus each of the four triangles has (ordinary) area `1/2`, and the
trivial counting upper bound `C(4,3) = 4` for four points is attained.

Faithfulness of the ℚ² model: the witness configuration has integer
coordinates, hence lives in `ℚ² ⊂ ℝ²`, and the doubled signed area is a
polynomial with integer coefficients in the coordinates, so the ℚ²
statement computes exactly the same values as its ℝ² counterpart.  The
catalogued problem is about finite planar point sets (in the real
plane); this rational model realizes one concrete real-plane
configuration.

It does NOT address the general extremal question (the maximum number
of equal-area triangles over all `n`-point sets, for arbitrary `n`),
does not resolve the catalogued open problem, and makes no award claim.

Mathematical area: Geometry / Distance geometry.
Problem posed: no later than 1971 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).

Proof notes
-----------
* Work in `ℚ × ℚ` rather than `ℝ × ℝ` so that the whole statement is
  decidable and the proof is a finite computation (`decide`); see the
  faithfulness remark above.  On this toolchain `norm_num` is the most
  robust tactic for `ℚ` arithmetic, and it is used for the four
  explicitly listed triangles.
* `|·|` is Mathlib's general `abs`; on `ℚ` it is the usual absolute
  value.
* The cardinality part `s.card = 4` of the `Finset` literal is decided
  directly.  For the area part, a direct `decide` on the quantified
  statement gets stuck in kernel reduction of `|·|` (the `ℚ` decidability
  of `≤` behind `abs` does not fully reduce under the
  `Finset.decidableDforallFinset` instance on this toolchain), so instead
  each of `a`, `b`, `c` is case-split over the four vertices and the
  resulting (at most `4³ = 64`) branches are closed by `simp_all` (which
  unfolds `area2` and computes over the literal coordinates): the
  pairwise-distinctness hypotheses kill all degenerate branches, leaving
  the `4! = 24` orderings of the `4` genuine triangles, each reducing to
  a small rational computation.
-/

import Mathlib

/-- Twice the signed area of the triangle with vertices `a b c` in the
rational plane, i.e. the cross product of the vectors `b - a` and
`c - a`.  It is independent of the order of the vertices up to sign. -/
def area2 (a b c : ℚ × ℚ) : ℚ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- The four triangles determined by the unit-square vertices, listed
explicitly (one orientation each): all have absolute doubled area `1`,
i.e. ordinary area `1/2`. -/
theorem jsp000903_four_triangles :
    |area2 (0, 0) (1, 0) (1, 1)| = 1 ∧
      |area2 (0, 0) (1, 0) (0, 1)| = 1 ∧
      |area2 (0, 0) (1, 1) (0, 1)| = 1 ∧
      |area2 (1, 0) (1, 1) (0, 1)| = 1 := by
  norm_num [area2]

/-- **Explicit witness for JSP-000903 (`n = 4` attainment instance).**

There exists a set of four points in the plane — the vertices of the
unit square, `{(0,0), (1,0), (1,1), (0,1)}` — such that every triangle
formed by three pairwise distinct points of the set has the same
absolute (doubled) area `1`; equivalently, all `C(4,3) = 4` triangles
determined by the set have the same ordinary area `1/2`.

Scope: existence of an attainment instance for `n = 4` only.  The
general problem — the maximum number of equal-area triangles over all
`n`-point sets for arbitrary `n` — remains open. -/
theorem jsp000903 :
    ∃ s : Finset (ℚ × ℚ), s.card = 4 ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
        a ≠ b → b ≠ c → a ≠ c → |area2 a b c| = 1 :=
  ⟨{(0, 0), (1, 0), (1, 1), (0, 1)}, by decide, by
    intro a ha b hb c hc hab hbc hac
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl | ha <;>
      rcases hb with rfl | rfl | rfl | hb <;>
      rcases hc with rfl | rfl | rfl | hc <;>
      simp_all [area2]⟩

#print axioms jsp000903
#print axioms jsp000903_four_triangles
