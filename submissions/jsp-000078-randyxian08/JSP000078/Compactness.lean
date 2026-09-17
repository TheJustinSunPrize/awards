/-
SPDX-License-Identifier: Apache-2.0

A formalization prepared with OpenAI Codex assistance on 2026-09-17.
See VERIFICATION.md for the actual verification evidence and its limits.

The compactness input is Mathlib's Rado selection theorem (Bhavik Mehta).
No originality is claimed for graph-coloring compactness.
-/
import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

namespace JSP000078

universe u

/-- Finite colorings of every finite induced subgraph imply a global coloring.
There is no finiteness or countability hypothesis on the vertex type.
The statement also includes the zero-color case. -/
theorem colorable_of_finite_induced
    {V : Type u} (G : SimpleGraph V) (n : ℕ)
    (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) :
    G.Colorable n := by
  classical
  let C (s : Finset V) : (G.induce (s : Set V)).Coloring (Fin n) :=
    (h s).some
  obtain ⟨χ, hχ⟩ :=
    Finset.rado_selection_subtype (β := fun _ : V => Fin n)
      (fun s x => C s x)
  refine ⟨SimpleGraph.Coloring.mk χ ?_⟩
  intro v w hvw
  let s : Finset V := {v, w}
  have hv : v ∈ s := by simp [s]
  have hw : w ∈ s := by simp [s]
  obtain ⟨t, hst, hagree⟩ := hχ s
  have hvχ : χ v = C t ⟨v, hst hv⟩ := hagree ⟨v, hv⟩
  have hwχ : χ w = C t ⟨w, hst hw⟩ := hagree ⟨w, hw⟩
  rw [hvχ, hwχ]
  exact (C t).valid
    (show (G.induce (t : Set V)).Adj ⟨v, hst hv⟩ ⟨w, hst hw⟩ from hvw)

/-- A finite obstruction exists whenever a fixed finite number of colors
cannot color the whole graph. -/
theorem exists_finite_induced_not_colorable
    {V : Type u} (G : SimpleGraph V) (n : ℕ)
    (h : ¬ G.Colorable n) :
    ∃ s : Finset V, ¬ (G.induce (s : Set V)).Colorable n := by
  classical
  by_contra hnone
  push Not at hnone
  exact h (colorable_of_finite_induced G n hnone)

/-- A bound by `n+1` which is not attained is a bound by `n`.
This avoids using subtraction on extended natural numbers. -/
theorem colorable_pred_of_bound_and_ne
    {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (hupper : G.chromaticNumber ≤ ((n + 1 : ℕ) : ℕ∞))
    (hne : G.chromaticNumber ≠ ((n + 1 : ℕ) : ℕ∞)) :
    G.Colorable n := by
  by_contra hnot
  have hc : G.Colorable (n + 1) :=
    SimpleGraph.chromaticNumber_le_iff_colorable.mp hupper
  have heq :=
    (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable
      (G := G) (n := n)).2 ⟨hc, hnot⟩
  exact hne (by simpa only [Nat.cast_add, Nat.cast_one] using heq)

end JSP000078
