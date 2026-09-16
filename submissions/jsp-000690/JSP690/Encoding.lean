import JSP690.Definitions

/-! The representation is a finite set system: vertex enumerations have no
duplicates, and two edges are equal exactly when their vertex sets agree. -/

namespace JSP690

theorem edgeVertices_nodup {n : Nat} (e : Edge n) : (edgeVertices e).Nodup := by
  exact (List.nodup_finRange n).filter _

theorem edge_eq_iff_vertices {n : Nat} (e f : Edge n) :
    e = f ↔ ∀ v : Vertex n, v ∈ edgeVertices e ↔ v ∈ edgeVertices f := by
  constructor
  · intro h
    subst f
    exact fun _ => Iff.rfl
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hv := h ⟨i, hi⟩
    simp only [mem_edgeVertices] at hv
    exact Bool.eq_iff_iff.mpr hv

end JSP690
