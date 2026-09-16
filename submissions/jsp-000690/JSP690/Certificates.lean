import JSP690.Witness

/-! Closed finite certificates. Every `decide` is checked by Lean's kernel;
no external search result is assumed and no native decision tactic is used. -/

namespace JSP690

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem witness_edge_count : witness.length = 22 := by decide

theorem witness_simple : Simple witness := by
  show witness.Nodup
  decide

theorem witness_three_uniform : Uniform witness 3 := by decide

theorem witness_degrees :
    ∀ v : Vertex 9, degree witness v = if v.val = 0 then 10 else 7 := by
  decide

theorem witness_min_degree : ∀ v : Vertex 9, 7 ≤ degree witness v := by
  intro v
  rw [witness_degrees]
  split <;> omega

theorem witness_attains_degree_seven : degree witness (1 : Vertex 9) = 7 := by
  decide

theorem threeColor_proper : ProperColoring witness threeColor := by decide

theorem witness_three_colorable : Colorable witness 3 :=
  ⟨threeColor, threeColor_proper⟩

theorem edgeDeletionColor_proper :
    ∀ e ∈ witness, ProperColoring (deleteEdge witness e) (edgeDeletionColor e) := by
  decide

theorem witness_edge_deletion_colorable :
    ∀ e ∈ witness, Colorable (deleteEdge witness e) 2 := by
  intro e he
  exact ⟨edgeDeletionColor e, edgeDeletionColor_proper e he⟩

theorem vertexDeletionColor_proper :
    ∀ v : Vertex 9, ProperColoring (deleteVertex witness v) (vertexDeletionColor v) := by
  decide

theorem witness_vertex_deletion_colorable :
    ∀ v : Vertex 9, Colorable (deleteVertex witness v) 2 := by
  intro v
  exact ⟨vertexDeletionColor v, vertexDeletionColor_proper v⟩

end JSP690
