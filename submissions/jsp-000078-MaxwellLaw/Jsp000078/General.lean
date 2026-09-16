/-
Copyright 2026 MaxwellLaw.
Copyright 2026 The Formal Conjectures Authors (the final theorem statement).
Released under Apache 2.0 license as described in the file LICENSE.

Formalization assisted by OpenAI Codex. The finite theorem is imported unchanged
from plby/lean-proofs, whose header credits András Gyárfás for the mathematics
and Codex / GPT-5.6 Sol for the formalization. Only the extension and bridges in
this module are new to this submission. See REFERENCES.md and vendor-manifest.json.
-/
import ErdosProblems.Erdos58
import Jsp000078.Compactness
import Jsp000078.CycleLengths

namespace Jsp000078

open scoped SimpleGraph

/-- The existing finite proof and Formal Conjectures use exactly the same
odd simple cycles; only the order of the two conjuncts differs. -/
theorem oddCycleLengths_eq {V : Type*} (G : SimpleGraph V) :
    Erdos58.oddCycleLengths G = G.oddCycleLengths := by
  ext n
  exact and_comm

/-- Gyárfás's bound and equality characterization for arbitrary vertex types.
The finite core is `Erdos58.erdos_58`; the extension uses compactness twice. -/
theorem erdos_58_encard {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) := by
  classical
  have hfinite (s : Finset V) :=
    Erdos58.erdos_58 (G.induce (s : Set V)) k
      ((Set.encard_mono (Erdos58.oddCycleLengths_induce_subset G (s : Set V))).trans hk)
  have hcolor : G.Colorable (2 * k + 2) :=
    colorable_of_finite_induced G _ fun s =>
      SimpleGraph.chromaticNumber_le_iff_colorable.mp (hfinite s).1
  have hupper := hcolor.chromaticNumber_le
  refine ⟨hupper, ?_⟩
  constructor
  · intro heq
    by_contra hcopy
    have hsmall : G.Colorable (2 * k + 1) := by
      apply colorable_of_finite_induced
      intro s
      have hne : (G.induce (s : Set V)).chromaticNumber ≠
          ((2 * k + 2 : ℕ) : ℕ∞) := by
        intro hs
        exact hcopy (((hfinite s).2.mp hs).trans
          (SimpleGraph.Embedding.induce (G := G) (s : Set V)).toCopy.isContained)
      have hlt := lt_of_le_of_ne (hfinite s).1 hne
      apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
      apply (ENat.lt_add_one_iff (ENat.natCast_ne_top (2 * k + 1))).mp
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        add_assoc, one_add_one_eq_two] using hlt
    have hle := hsmall.chromaticNumber_le
    rw [heq] at hle
    have : 2 * k + 2 ≤ 2 * k + 1 := by exact_mod_cast hle
    omega
  · intro hcopy
    exact le_antisymm hupper
      (Erdos58.completeGraph_card_le_chromaticNumber_of_isContained hcopy)

/-- The full statement from Formal Conjectures / Erdős 58: arbitrary vertex
type, finitely many odd cycle lengths, both directions of the equality case. -/
theorem erdos_58 :
    ∀ {V : Type*} (G : SimpleGraph V) (k : ℕ),
      G.oddCycleLengths.Finite →
      G.oddCycleLengths.ncard ≤ k →
        G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
          (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) := by
  intro V G k hfin hk
  have henc : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞) := by
    rw [oddCycleLengths_eq, ← hfin.cast_ncard_eq]
    exact_mod_cast hk
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    erdos_58_encard G k henc

end Jsp000078
