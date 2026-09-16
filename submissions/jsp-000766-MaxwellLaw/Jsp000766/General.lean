/-
Copyright 2026 MaxwellLaw.
Released under Apache 2.0 license as described in the file LICENSE.

Formalization assisted by OpenAI Codex. The finite theorem is imported unchanged
from plby/lean-proofs, whose header credits Jon Folkman for the mathematics and
Codex / GPT-5.6 Sol for the formalization. This file extends that result to
arbitrary vertex types. The finite-subgraph equivalence generalizes the upstream
hasLargeIndependentSets_iff_onFinsets bridge. See REFERENCES.md and source-manifest.json.
-/
import ErdosProblems.Erdos922
import Jsp000766.Compactness

namespace Jsp000766

open SimpleGraph
open scoped ENat

/-- The local independence bound passes to every induced subgraph, including
one on an infinite vertex set. The witnesses themselves remain finite. -/
theorem local_independence_induce {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : Erdos922.HasLargeIndependentSetsOnFinsets G k) (s : Set V) :
    Erdos922.HasLargeIndependentSetsOnFinsets (G.induce s) k := by
  classical
  intro T
  let e : s ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨I, hIT, hI, hcard⟩ := h (T.map e)
  have hIs : ∀ v ∈ I, v ∈ s := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp (hIT hv)
    exact w.property
  let J : Finset s := I.subtype (fun v => v ∈ s)
  have hJcard : J.card = I.card := by
    simp only [J, Finset.card_subtype, Finset.filter_eq_self.mpr hIs]
  refine ⟨J, ?_, ?_, ?_⟩
  · intro v hv
    have hvI : v.val ∈ I := by simpa only [J, Finset.mem_subtype] using hv
    obtain ⟨w, hw, hweq⟩ := Finset.mem_map.mp (hIT hvI)
    have hwv : w = v := Subtype.ext hweq
    simpa only [hwv] using hw
  · rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    change a ∈ J at ha
    change b ∈ J at hb
    have haI : a.val ∈ I := by simpa only [J, Finset.mem_subtype] using ha
    have hbI : b.val ∈ I := by simpa only [J, Finset.mem_subtype] using hb
    exact fun hadj => hI haI hbI (Subtype.coe_ne_coe.mpr hab) hadj
  · simpa only [Finset.card_map, hJcard] using hcard

/-- Folkman's finite theorem and de Bruijn--Erdős compactness produce an
actual coloring by the fixed palette `Fin (k + 2)` for any vertex type. -/
theorem erdos_922_colorable {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ S : Finset V, ∃ I : Finset V,
      I ⊆ S ∧ G.IsIndepSet I ∧ S.card ≤ 2 * I.card + k) :
    G.Colorable (k + 2) := by
  apply colorable_of_finite_induced
  intro S
  apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
  exact Erdos922.erdos_922 (G.induce (S : Set V)) k
    (Erdos922.hasLargeIndependentSets_iff_onFinsets.mpr
      (local_independence_induce h (S : Set V)))

/-- JSP-000766 / Erdős 922 for arbitrary, possibly infinite graphs.
The inequality is integral: no truncation or rounding of `(n - k) / 2` is used. -/
theorem erdos_922 {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ S : Finset V, ∃ I : Finset V,
      I ⊆ S ∧ G.IsIndepSet I ∧ S.card ≤ 2 * I.card + k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) :=
  (erdos_922_colorable G k h).chromaticNumber_le

/-- A literal formulation on every subgraph with finitely many vertices.
Edges may be deleted: these subgraphs need not be induced or spanning. -/
def HasLargeIndependentSetsOnFiniteSubgraphs {V : Type*}
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, H.verts.Finite → ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

/-- The finite-induced-set formulation is equivalent to the literal condition
on all finite subgraphs, without any finiteness assumption on the ambient graph. -/
theorem finite_subgraphs_iff_finsets {V : Type*} {G : SimpleGraph V} {k : ℕ} :
    HasLargeIndependentSetsOnFiniteSubgraphs G k ↔
      Erdos922.HasLargeIndependentSetsOnFinsets G k := by
  classical
  constructor
  · intro h S
    let H : G.Subgraph := (⊤ : G.Subgraph).induce (↑S : Set V)
    have hH : H.verts.Finite := by simpa only [H, SimpleGraph.Subgraph.induce_verts] using S.finite_toSet
    obtain ⟨J, hJ, hcard⟩ := h H hH
    let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨I, ?_, ?_, ?_⟩
    · intro v hv
      simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact w.property
    · have himage : G.IsIndepSet (Subtype.val '' (↑J : Set H.verts)) :=
        (SimpleGraph.isIndepSet_induce (G := G)).mp hJ
      simpa only [I, Finset.coe_map, Function.Embedding.coeFn_mk] using himage
    · simpa only [H, SimpleGraph.Subgraph.induce_verts, Set.ncard_coe_finset,
        I, Finset.card_map] using hcard
  · intro h H hH
    let : Fintype H.verts := hH.fintype
    let S : Finset V := H.verts.toFinset
    obtain ⟨I, hIS, hI, hcard⟩ := h S
    let J : Finset H.verts := I.subtype (fun v => v ∈ H.verts)
    refine ⟨J, ?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      change a ∈ J at ha
      change b ∈ J at hb
      have haI : a.val ∈ I := by simpa only [J, Finset.mem_subtype] using ha
      have hbI : b.val ∈ I := by simpa only [J, Finset.mem_subtype] using hb
      exact fun hAdj => hI haI hbI (Subtype.coe_ne_coe.mpr hab)
        (H.coe_adj_sub a b hAdj)
    · have hIfilter : I.filter (fun v => v ∈ H.verts) = I := by
        exact Finset.filter_eq_self.mpr fun v hv => by
          have : v ∈ S := hIS hv
          simpa only [S, Set.mem_toFinset] using this
      have hJcard : J.card = I.card := by
        simp only [J, Finset.card_subtype, hIfilter]
      rw [Set.ncard_eq_toFinset_card']
      simpa only [S, hJcard] using hcard

/-- The same global coloring bound from the literal finite-subgraph hypothesis. -/
theorem erdos_922_of_finite_subgraphs {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : HasLargeIndependentSetsOnFiniteSubgraphs G k) :
    G.Colorable (k + 2) ∧ G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  have hc := erdos_922_colorable G k (finite_subgraphs_iff_finsets.mp h)
  exact ⟨hc, hc.chromaticNumber_le⟩

end Jsp000766
