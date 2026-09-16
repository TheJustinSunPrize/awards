import Statement

namespace JSP000840

def badGraphs : Finset Graph :=
  Finset.univ.filter (fun G : Graph => G.card = 5 ∧ triangleCount G < 2)

theorem no_bad_graphs : badGraphs = ∅ := by
  decide

theorem solution : targetStatement := by
  intro G hcard
  by_contra htri
  have hbad : G ∈ badGraphs := by
    simp only [badGraphs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcard, Nat.lt_of_not_ge htri⟩
  rw [no_bad_graphs] at hbad
  simp at hbad

end JSP000840
