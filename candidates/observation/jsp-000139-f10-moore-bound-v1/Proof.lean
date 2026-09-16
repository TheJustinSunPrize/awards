import «Statement»

open scoped BigOperators

namespace JSP000139

noncomputable section

private theorem mem_neighbors_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v := by
  simp [neighbors]

private theorem card_neighbors_sub_singleton_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V) (D : ℕ)
    (hdegree : ∀ v : V, degree G v ≤ D)
    {root y : V} (hy : y ∈ neighbors G root) :
    (neighbors G y \ {root}).card ≤ D - 1 := by
  have hroot : root ∈ neighbors G y := by
    apply (mem_neighbors_iff G y root).mpr
    exact G.symm ((mem_neighbors_iff G root y).mp hy)
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hroot]
  have hdeg : (neighbors G y).card ≤ D := by
    simpa [degree] using hdegree y
  omega

private theorem moore_bound_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraphOn V)
    (D : ℕ)
    (hdegree : ∀ v : V, degree G v ≤ D)
    (hdiam : ∀ root : V, WithinTwoFrom G root) :
    Fintype.card V ≤ D ^ 2 + 1 := by
  classical
  let root : V := Classical.choice (inferInstance : Nonempty V)
  let N : Finset V := neighbors G root
  let T : Finset V := N.biUnion (fun y => neighbors G y \ {root})
  have hcover : (Finset.univ : Finset V) ⊆ ({root} ∪ N) ∪ T := by
    intro x hx
    by_cases hxr : x = root
    · subst x
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self root))))
    · rcases hdiam root x with h | h | ⟨y, hyroot, hyx⟩
      · exact (hxr h).elim
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact (mem_neighbors_iff G root x).mpr h
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_biUnion.mpr
        refine ⟨y, (mem_neighbors_iff G root y).mpr hyroot, ?_⟩
        apply Finset.mem_sdiff.mpr
        exact ⟨(mem_neighbors_iff G y x).mpr hyx, by
          intro hxroot
          exact hxr (Finset.mem_singleton.mp hxroot)⟩
  have hT : T.card ≤ D * (D - 1) := by
    have hsum :
        T.card ≤ ∑ y ∈ N, (neighbors G y \ {root}).card := by
      change
        (N.biUnion (fun y => neighbors G y \ {root})).card ≤
          ∑ y ∈ N, (neighbors G y \ {root}).card
      exact Finset.card_biUnion_le
    have hsum' :
        (∑ y ∈ N, (neighbors G y \ {root}).card) ≤
          ∑ y ∈ N, (D - 1) := by
      apply Finset.sum_le_sum
      intro y hy
      exact card_neighbors_sub_singleton_le G D hdegree hy
    have hconst : (∑ y ∈ N, (D - 1)) = N.card * (D - 1) := by
      simp [Finset.sum_const]
    have hN : N.card ≤ D := by
      simpa [N, degree] using hdegree root
    calc
      T.card ≤ ∑ y ∈ N, (neighbors G y \ {root}).card := hsum
      _ ≤ ∑ y ∈ N, (D - 1) := hsum'
      _ = N.card * (D - 1) := hconst
      _ ≤ D * (D - 1) := Nat.mul_le_mul_right (D - 1) hN
  have hcard_union :
      (({root} ∪ N) ∪ T).card ≤ 1 + D + D * (D - 1) := by
    have hfirst : ({root} ∪ N).card ≤ 1 + D := by
      calc
        ({root} ∪ N).card ≤ ({root} : Finset V).card + N.card :=
          Finset.card_union_le _ _
        _ = 1 + N.card := by simp
        _ ≤ 1 + D := Nat.add_le_add_left (by simpa [N, degree] using hdegree root) 1
    calc
      (({root} ∪ N) ∪ T).card ≤ ({root} ∪ N).card + T.card :=
        Finset.card_union_le _ _
      _ ≤ (1 + D) + D * (D - 1) :=
        Nat.add_le_add hfirst hT
      _ = 1 + D + D * (D - 1) := by omega
  have hcard : Fintype.card V ≤ 1 + D + D * (D - 1) := by
    calc
      Fintype.card V = (Finset.univ : Finset V).card := by simp
      _ ≤ (({root} ∪ N) ∪ T).card := Finset.card_le_card hcover
      _ ≤ 1 + D + D * (D - 1) := hcard_union
  calc
    Fintype.card V ≤ 1 + D + D * (D - 1) := hcard
    _ = D ^ 2 + 1 := by
      calc
        1 + D + D * (D - 1) = 1 + D + (D * D - D) := by
          simp [Nat.mul_sub_left_distrib]
        _ = D * D + 1 := by
          have hsub : D * D - D + D = D * D :=
            Nat.sub_add_cancel (Nat.le_mul_self D)
          omega
        _ = D ^ 2 + 1 := by rw [pow_two]

/-- The Moore bound: a finite graph of diameter at most two and maximum degree
at most `D` has at most `D^2 + 1` vertices.  Triangle-freeness is included as
an explicit source hypothesis, although this counting bound does not use it. -/
theorem moore_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V)
    (_htriangle : TriangleFree G)
    (D : ℕ)
    (hdegree : ∀ v : V, degree G v ≤ D)
    (hdiam : ∀ root : V, WithinTwoFrom G root) :
    Fintype.card V ≤ D ^ 2 + 1 := by
  classical
  by_cases hV : Nonempty V
  · exact @moore_bound_of_nonempty V _ _ hV G D hdegree hdiam
  · have hI : IsEmpty V := not_nonempty_iff.mp hV
    have hcard0 : Fintype.card V = 0 := @Fintype.card_eq_zero V _ hI
    omega

end
end JSP000139
