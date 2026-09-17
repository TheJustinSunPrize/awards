/- Local 20-vertex adaptation of PR #190, commit 4022d2df0f941a12f497d5045b75995e0cf8f883.
   Upstream formalization: jinkaizhang236-sketch / Justin Sun Prize contributors.
   Original mathematical construction: Paul W. Dyson and Brendan D. McKay.
   See THIRD_PARTY_NOTICES.md for exact reuse and changes. -/
import Graph20
import Mathlib.Combinatorics.SimpleGraph.Finite
set_option maxRecDepth 4096
namespace Graph20Proof
open RegularCertificate

theorem symmetric_data : ∀ i j : Fin 20, j ∈ neighbors i ↔ i ∈ neighbors j := by
  decide +kernel

theorem irreflexive_data : ∀ i : Fin 20, i ∉ neighbors i := by
  decide +kernel

def graph : SimpleGraph (Fin 20) where
  Adj i j := j ∈ neighbors i
  symm := ⟨fun i j h => (symmetric_data i j).mp h⟩
  loopless := ⟨irreflexive_data⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem neighbors_eq (v : Fin 20) : graph.neighborFinset v = neighbors v := by
  ext w
  exact graph.mem_neighborFinset v w

theorem induced_degree (T : Finset (Fin 20)) (v : (T : Set (Fin 20))) :
    (graph.induce (T : Set (Fin 20))).degree v = degree neighbors T v.val := by
  have h := congrArg Finset.card (graph.map_neighborFinset_induce v)
  simp only [Finset.card_map, neighbors_eq, Finset.toFinset_coe] at h
  change (SimpleGraph.neighborFinset _ _).card = _
  convert h using 1
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  all_goals rfl

theorem regular_correspondence (T : Finset (Fin 20)) (d : Nat) :
    (graph.induce (T : Set (Fin 20))).IsRegularOfDegree d ↔ RegularOn neighbors T d := by
  constructor
  · intro h v hv
    exact (induced_degree T ⟨v, hv⟩).symm.trans (h.degree_eq ⟨v, hv⟩)
  · intro h v
    exact (induced_degree T v).trans (h v.val v.property)

#print axioms regular_correspondence
end Graph20Proof
