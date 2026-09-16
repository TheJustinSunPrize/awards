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
import Degree11
import Degree12
import Degree13
import Degree14
import Degree15
import Degree16
import Degree17
import Degree18
import Degree19

namespace Graph20Proof
open RegularCertificate

theorem neighbor_card_lt : ∀ v : Fin 20, (neighbors v).card < 20 := by decide +kernel

theorem no_regular (T : Finset (Fin 20)) (hT : 6 ≤ T.card) (d : Nat) :
    ¬ RegularOn neighbors T d := by
  intro hreg
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hle : degree neighbors T v ≤ (neighbors v).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hd : d < 20 := by
    have hc := neighbor_card_lt v
    rw [hreg v hv] at hle
    omega
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 ∨ d = 16 ∨ d = 17 ∨ d = 18 ∨ d = 19 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- This explicit 20-vertex graph has no regular induced subgraph of order at least six. -/
theorem graph20_no_regular_induced (T : Finset (Fin 20)) (hT : 6 ≤ T.card) (d : Nat) :
    ¬ (graph.induce (T : Set (Fin 20))).IsRegularOfDegree d := by
  intro h
  exact no_regular T hT d ((regular_correspondence T d).mp h)

/-- A standard finite graph witness for the known lower bound N_{≥6} ≥ 21.
This does not establish equality or solve the open asymptotic problem. -/
theorem exists_graph20 : ∃ G : SimpleGraph (Fin 20),
    ∃ inst : DecidableRel G.Adj,
    letI := inst
    ∀ T : Finset (Fin 20), 6 ≤ T.card →
      ∀ d : Nat, ¬ (G.induce (T : Set (Fin 20))).IsRegularOfDegree d := by
  exact ⟨graph, inferInstance, graph20_no_regular_induced⟩

#print axioms graph20_no_regular_induced
#print axioms exists_graph20
end Graph20Proof
