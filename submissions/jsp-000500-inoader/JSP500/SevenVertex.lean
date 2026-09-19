import JSP500.WeightedLightEdge
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Independence number at most five excludes a one-vertex edge cover
on seven vertices. -/
theorem noSingleCover_of_seven (hn : Fintype.card V = 7)
    (hα : Gᶜ.CliqueFree 6) : NoSingleCover G := by
  classical
  intro w
  by_contra h
  push Not at h
  apply hα (Finset.univ.erase w)
  constructor
  · intro u hu v hv huv
    have huw : u ≠ w := (Finset.mem_erase.mp hu).1
    have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
    exact ⟨huv, fun hadj => hvw (h u v hadj huw)⟩
  · simp [hn]

/-- The exact first weighted finite premise of the r=7 argument. -/
theorem seven_vertex_light_edge_six (hn : Fintype.card V = 7)
    (hα : Gᶜ.CliqueFree 6) (z : V → Nat)
    (hm : 6 ≤ G.edgeFinset.card) (hb : G.edgeFinset.card + ∑ v, z v ≤ 8) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v + z u + z v ≤ 6 :=
  weighted_light_edge_six G z (noSingleCover_of_seven G hn hα) hm hb

/-- The exact second weighted finite premise of the r=7 argument. -/
theorem seven_vertex_light_edge_seven (hn : Fintype.card V = 7)
    (hα : Gᶜ.CliqueFree 6) (z : V → Nat)
    (hm : 6 ≤ G.edgeFinset.card) (hb : G.edgeFinset.card + ∑ v, z v ≤ 9) :
    ∃ u v, G.Adj u v ∧ G.degree u + G.degree v + z u + z v ≤ 7 :=
  weighted_light_edge_seven G z (noSingleCover_of_seven G hn hα) hm hb

end JSP500
