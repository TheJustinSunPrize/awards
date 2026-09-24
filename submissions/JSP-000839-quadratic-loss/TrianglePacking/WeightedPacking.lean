import TrianglePacking.Basic

/-!
# A weighted bound for an edge-disjoint packing

Every oriented edge is counted at most once in a family with disjoint `arcs`.
Natural-number weights give a bound by the weight of all ordered pairs of
distinct vertices. This argument does not assume that the family is maximal.
-/

namespace TrianglePacking

open scoped BigOperators

/-- Pairwise disjoint finite edge sets cannot use more weight than all edges. -/
theorem sum_arcs_le_sum_offDiag {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V))
    (hP : (P : Set (Finset V)).Pairwise (fun T U => Disjoint (arcs T) (arcs U)))
    (w : V × V → ℕ) :
    (∑ T ∈ P, ∑ e ∈ arcs T, w e) ≤ ∑ e ∈ Finset.univ.offDiag, w e := by
  have hsubset : P.biUnion arcs ⊆ (Finset.univ : Finset V).offDiag := by
    intro e he
    obtain ⟨T, _, heT⟩ := Finset.mem_biUnion.mp he
    exact Finset.offDiag_mono (Finset.subset_univ T) heT
  calc
    (∑ T ∈ P, ∑ e ∈ arcs T, w e) = ∑ e ∈ P.biUnion arcs, w e :=
      (Finset.sum_biUnion hP).symm
    _ ≤ ∑ e ∈ Finset.univ.offDiag, w e :=
      Finset.sum_le_sum_of_subset hsubset

/-- A uniform lower bound on the weight of each member bounds the family size. -/
theorem weighted_bound_of_pairwise {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V))
    (hP : (P : Set (Finset V)).Pairwise (fun T U => Disjoint (arcs T) (arcs U)))
    (w : V × V → ℕ) (L : ℕ)
    (hL : ∀ T ∈ P, L ≤ ∑ e ∈ arcs T, w e) :
    L * P.card ≤ ∑ e ∈ Finset.univ.offDiag, w e := by
  calc
    L * P.card = ∑ _T ∈ P, L := by simp [Nat.mul_comm]
    _ ≤ ∑ T ∈ P, ∑ e ∈ arcs T, w e := Finset.sum_le_sum hL
    _ ≤ ∑ e ∈ Finset.univ.offDiag, w e := sum_arcs_le_sum_offDiag P hP w

/-- Weighted packing bound, directly callable from an `IsPacking` proof. -/
theorem IsPacking.weighted_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {P : Finset (Finset V)} (hP : IsPacking G P)
    (w : V × V → ℕ) (L : ℕ)
    (hL : ∀ T ∈ P, L ≤ ∑ e ∈ arcs T, w e) :
    L * P.card ≤ ∑ e ∈ Finset.univ.offDiag, w e :=
  weighted_bound_of_pairwise P hP.2 w L hL

end TrianglePacking
