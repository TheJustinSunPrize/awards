import JSP500.ColoringBounds
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma triangleFree_degree_le (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) :
    ∀ v, G.degree v ≤ 6 := by
  intro v
  have hcl : Gᶜ.IsClique (G.neighborFinset v) := by
    rw [G.isClique_compl]
    simpa using G.isIndepSet_neighborSet_of_triangleFree ht v
  have := clique_card_lt_of_cliqueFree hi hcl
  rw [G.card_neighborFinset_eq_degree] at this
  omega

/-- The 14-vertex terminal obstruction: density 42 is incompatible
with being triangle-free and having independence number at most six. -/
theorem terminal_core_fourteen (hn : Fintype.card V = 14)
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7)
    (he : 42 ≤ G.edgeFinset.card) : False := by
  classical
  have hdeg := triangleFree_degree_le G ht hi
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hu : (∑ v, G.degree v) ≤ ∑ _v : V, 6 :=
    Finset.sum_le_sum (fun v _ => hdeg v)
  have htotal : (∑ v, G.degree v) = ∑ _v : V, 6 := by
    simp only [Finset.sum_const, Finset.card_univ, hn, smul_eq_mul] at hu ⊢
    omega
  have hreg : ∀ v, G.degree v = 6 := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun v (_ : v ∈ (Finset.univ : Finset V)) => hdeg v)).mp htotal
    exact fun v => hh v (Finset.mem_univ v)
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hmin : 6 ≤ G.minDegree := G.le_minDegree_of_forall_le_degree 6 (fun v => (hreg v).ge)
  have hcol : G.Colorable 2 := G.colorable_of_cliqueFree_lt_minDegree ht (by simp [hn]; omega)
  have hcard := card_le_of_colorable_and_independence hcol hi
  omega

end JSP500
