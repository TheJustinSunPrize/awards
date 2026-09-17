import BipartiteC4.Counts

namespace BipartiteC4

def canonicalVertex (a b k : ℕ) (ha : 2*k ≤ a) (hb : 2*k ≤ b)
    (p : Fin k × Fin 4) : Vertex a b :=
      ![Sum.inl ⟨2*p.1.val, by omega⟩,
        Sum.inr ⟨2*p.1.val, by omega⟩,
        Sum.inl ⟨2*p.1.val+1, by omega⟩,
        Sum.inr ⟨2*p.1.val+1, by omega⟩] p.2

/-- Pair consecutive left and right vertices to realize every feasible size. -/
def canonicalPacking (a b k : ℕ) (ha : 2*k ≤ a) (hb : 2*k ≤ b) :
    Packing (graph a b) k where
  vertices := {
    toFun := canonicalVertex a b k ha hb
    inj' := by
      rintro ⟨i,j⟩ ⟨l,m⟩ h
      fin_cases j <;> fin_cases m <;>
        simp [canonicalVertex, Fin.ext_iff] at h ⊢ <;> omega }
  adjacent i j := by
    change (graph a b).Adj (canonicalVertex a b k ha hb (i,j))
      (canonicalVertex a b k ha hb (i,j+1))
    fin_cases j <;> simp [canonicalVertex, graph, completeBipartiteGraph]

/-- Exact feasibility, including empty classes and the empty packing. -/
theorem hasPacking_iff {a b k : ℕ} :
    HasPacking (graph a b) k ↔ 2*k ≤ a ∧ 2*k ≤ b := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.left_bound,p.right_bound⟩
  · rintro ⟨ha,hb⟩
    exact ⟨canonicalPacking a b k ha hb⟩

/-- The maximum number is exactly the smaller half-class size, rounded down. -/
theorem exact_capacity (a b k : ℕ) :
    HasPacking (graph a b) k ↔ k ≤ min (a/2) (b/2) := by
  rw [hasPacking_iff]
  omega

/-- The upper bound is attained by an explicit family of genuine C4 copies. -/
theorem maximum_attained (a b : ℕ) :
    HasPacking (graph a b) (min (a/2) (b/2)) ∧
    ∀ k, HasPacking (graph a b) k → k ≤ min (a/2) (b/2) := by
  exact ⟨(exact_capacity ..).mpr le_rfl, fun _ h => (exact_capacity ..).mp h⟩

end BipartiteC4
