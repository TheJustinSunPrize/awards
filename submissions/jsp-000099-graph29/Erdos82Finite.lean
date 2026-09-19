import GraphBridge
import Degree0
import Degree1
import Degree2
import Degree3
import Degree4
import Degree5
import Degree6
import Degree7
import Degree8
import Degree9
import Degree10
import HighDegrees

namespace Erdos82Finite
open RegularCertificate

theorem neighbor_card_lt : ∀ v : Fin 29, (neighbors v).card < 29 := by
  decide +kernel

theorem no_regular (T : Finset (Fin 29)) (hT : 7 ≤ T.card) (d : Nat) :
    ¬ RegularOn neighbors T d := by
  intro hreg
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hle : degree neighbors T v ≤ (neighbors v).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hd : d < 29 := by
    have hc := neighbor_card_lt v
    rw [hreg v hv] at hle
    omega
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 ∨ d = 16 ∨ d = 17 ∨ d = 18 ∨ d = 19 ∨ d = 20 ∨ d = 21 ∨ d = 22 ∨ d = 23 ∨ d = 24 ∨ d = 25 ∨ d = 26 ∨ d = 27 ∨ d = 28 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_regular_0 T hT hreg
  · exact no_regular_1 T hT hreg
  · exact no_regular_2 T hT hreg
  · exact no_regular_3 T hT hreg
  · exact no_regular_4 T hT hreg
  · exact no_regular_5 T hT hreg
  · exact no_regular_6 T hT hreg
  · exact no_regular_7 T hT hreg
  · exact no_regular_8 T hT hreg
  · exact no_regular_9 T hT hreg
  · exact no_regular_10 T hT hreg
  · exact no_regular_11 T hT hreg
  · exact no_regular_12 T hT hreg
  · exact no_regular_13 T hT hreg
  · exact no_regular_14 T hT hreg
  · exact no_regular_15 T hT hreg
  · exact no_regular_16 T hT hreg
  · exact no_regular_17 T hT hreg
  · exact no_regular_18 T hT hreg
  · exact no_regular_19 T hT hreg
  · exact no_regular_20 T hT hreg
  · exact no_regular_21 T hT hreg
  · exact no_regular_22 T hT hreg
  · exact no_regular_23 T hT hreg
  · exact no_regular_24 T hT hreg
  · exact no_regular_25 T hT hreg
  · exact no_regular_26 T hT hreg
  · exact no_regular_27 T hT hreg
  · exact no_regular_28 T hT hreg

/-- The concrete Dyson--McKay graph has no regular induced subgraph of order at least seven. -/
theorem graph29_no_regular_induced (T : Finset (Fin 29)) (hT : 7 ≤ T.card) (d : Nat) :
    ¬ (graph.induce (T : Set (Fin 29))).IsRegularOfDegree d := by
  intro h
  exact no_regular T hT d ((regular_correspondence T d).mp h)

/-- Standard graph-language witness for the known lower bound N_{≥7} ≥ 30.
This is a finite lower bound, not a solution of the open asymptotic conjecture. -/
theorem exists_graph29 : ∃ G : SimpleGraph (Fin 29),
    ∃ inst : DecidableRel G.Adj,
    letI := inst
    ∀ T : Finset (Fin 29), 7 ≤ T.card →
      ∀ d : Nat, ¬ (G.induce (T : Set (Fin 29))).IsRegularOfDegree d := by
  exact ⟨graph, inferInstance, graph29_no_regular_induced⟩

#print axioms graph29_no_regular_induced
#print axioms exists_graph29
end Erdos82Finite
