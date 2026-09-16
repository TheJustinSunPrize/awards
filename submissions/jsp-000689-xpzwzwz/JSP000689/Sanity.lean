import JSP000689.Main

namespace JSP000689

/-- A three-cycle, viewed as a two-uniform hypergraph. -/
def triangle : Finset (Finset (Fin 3)) := {{0, 1}, {1, 2}, {0, 2}}

theorem triangle_uniform : ∀ e ∈ triangle, e.card = 2 := by decide

theorem triangle_not_two_colorable : NotTwoColorable triangle := by
  unfold NotTwoColorable Mono triangle
  decide

theorem triangle_degree : ∀ v, degree triangle v = 2 := by decide

/-- Sanity check: the assumptions are inhabited by an ordinary odd cycle. -/
theorem triangle_application : ∃ v, (1 + 1 / 8 : ℝ) ^ 2 ≤ (degree triangle v : ℝ) :=
  erdos833 triangle 2 (by decide) triangle_uniform triangle_not_two_colorable

/-- A single edge of size at least two is two-colourable, as expected. -/
theorem single_edge_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (e : Finset V) (r : ℕ) (hr : 2 ≤ r) (he : e.card = r) :
    ¬ NotTwoColorable {e} := by
  classical
  apply not_not.mpr
  apply colorable {e} r hr (by simpa) 1 (by norm_num)
  intro v
  norm_num
  have hle : degree {e} v ≤ 1 := by
    unfold degree
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast hle

end JSP000689
