import JSP692.AlonCore

set_option autoImplicit false

/-!
All-parameter intersection, three-colourability, and active-vertex coverage
for Alon's construction. Each label is the half of a balanced partition
containing a fixed point p, so complementary halves share ONE new vertex.
-/

namespace JSP692

section Lifting
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

@[simp] theorem inl_mem_liftCore (x : X) (s : Finset X) :
    Sum.inl x ∈ liftCore (Y := Y) s ↔ x ∈ s := by
  simp [liftCore]

/-- A common core vertex remains a common vertex after lifting and adding labels. -/
theorem intersect_of_core {a b : Finset X} {e f : Finset (X ⊕ Y)}
    (hab : (a ∩ b).Nonempty)
    (ha : liftCore a ⊆ e) (hb : liftCore b ⊆ f) :
    (e ∩ f).Nonempty := by
  obtain ⟨x, hx⟩ := hab
  refine ⟨Sum.inl x, Finset.mem_inter.mpr ⟨ha ?_, hb ?_⟩⟩
  · exact (inl_mem_liftCore x a).mpr (Finset.mem_inter.mp hx).1
  · exact (inl_mem_liftCore x b).mpr (Finset.mem_inter.mp hx).2

end Lifting

section Canonical
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {p : X}

/-- The other half of a balanced partition has the same cardinality. -/
theorem canonical_complement_card (hsize : Fintype.card X = 2 * m)
    (y : BalancedLabels m p) :
    ((Finset.univ : Finset X) \ y.val).card = m := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ y.val)
  rw [Finset.card_univ, hsize, y.property.1] at h
  omega

/-- Every constructed edge is a core edge or one of the two edges of a label. -/
theorem canonical_edge_cases {e : Finset (X ⊕ BalancedLabels m p)}
    (he : e ∈ (canonicalGadget m p).graph) :
    (∃ a : Finset X, a.card = m + 1 ∧ e = liftCore a) ∨
      ∃ y : BalancedLabels m p,
        e = leftEdge (canonicalGadget m p) y ∨
        e = rightEdge (canonicalGadget m p) y := by
  classical
  change e ∈ (canonicalGadget m p).core.image liftCore ∪
    Finset.univ.biUnion (fun y =>
      {leftEdge (canonicalGadget m p) y, rightEdge (canonicalGadget m p) y}) at he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨a, (Finset.mem_powersetCard.mp ha).2, rfl⟩
  · obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp he
    exact Or.inr ⟨y, by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy⟩

theorem canonical_core_core (hsize : Fintype.card X = 2 * m)
    {a b : Finset X} (ha : a.card = m + 1) (hb : b.card = m + 1) :
    (liftCore (Y := BalancedLabels m p) a ∩ liftCore b).Nonempty := by
  have h : (a ∩ b).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ b) (by
        rw [Finset.card_univ, hsize, ha, hb]
        omega)
  exact intersect_of_core h (fun _ hv => hv) (fun _ hv => hv)

theorem canonical_core_left (hsize : Fintype.card X = 2 * m)
    {a : Finset X} (ha : a.card = m + 1) (y : BalancedLabels m p) :
    (liftCore a ∩ leftEdge (canonicalGadget m p) y).Nonempty := by
  have h : (a ∩ y.val).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ y.val) (by
        rw [Finset.card_univ, hsize, ha, y.property.1]
        omega)
  apply intersect_of_core h (fun _ hv => hv)
  intro v hv
  exact Finset.mem_insert_of_mem hv

theorem canonical_core_right (hsize : Fintype.card X = 2 * m)
    {a : Finset X} (ha : a.card = m + 1) (y : BalancedLabels m p) :
    (liftCore a ∩ rightEdge (canonicalGadget m p) y).Nonempty := by
  have h : (a ∩ ((Finset.univ : Finset X) \ y.val)).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ a) (Finset.subset_univ _) (by
        rw [Finset.card_univ, hsize, ha, canonical_complement_card hsize y]
        omega)
  apply intersect_of_core h (fun _ hv => hv)
  intro v hv
  exact Finset.mem_insert_of_mem hv

/-- Two chosen representatives both contain the distinguished core point. -/
theorem canonical_left_left (y z : BalancedLabels m p) :
    (leftEdge (canonicalGadget m p) y ∩
      leftEdge (canonicalGadget m p) z).Nonempty := by
  apply intersect_of_core (a := y.val) (b := z.val)
    ⟨p, Finset.mem_inter.mpr ⟨y.property.2, z.property.2⟩⟩
  · intro v hv
    exact Finset.mem_insert_of_mem hv
  · intro v hv
    exact Finset.mem_insert_of_mem hv

/-- Disjoint opposite halves must belong to the same balanced partition. -/
theorem canonical_left_right (y z : BalancedLabels m p) :
    (leftEdge (canonicalGadget m p) y ∩
      rightEdge (canonicalGadget m p) z).Nonempty := by
  classical
  by_cases h : (y.val ∩ ((Finset.univ : Finset X) \ z.val)).Nonempty
  · apply intersect_of_core h
    · intro v hv
      exact Finset.mem_insert_of_mem hv
    · intro v hv
      exact Finset.mem_insert_of_mem hv
  · have hsub : y.val ⊆ z.val := by
      intro x hx
      by_contra hxz
      exact h ⟨x, Finset.mem_inter.mpr
        ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxz⟩⟩⟩
    have heq : y.val = z.val := Finset.eq_of_subset_of_card_le hsub (by
      rw [y.property.1, z.property.1])
    have hyz : y = z := Subtype.ext heq
    subst z
    refine ⟨Sum.inr y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_self _ _

/-- Opposite representatives avoid p, so two such halves cannot be disjoint. -/
theorem canonical_right_right (hm : 0 < m) (hsize : Fintype.card X = 2 * m)
    (y z : BalancedLabels m p) :
    (rightEdge (canonicalGadget m p) y ∩
      rightEdge (canonicalGadget m p) z).Nonempty := by
  have hsub (w : BalancedLabels m p) :
      (Finset.univ : Finset X) \ w.val ⊆ Finset.univ.erase p := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    intro hxp
    exact (Finset.mem_sdiff.mp hx).2 (hxp.symm ▸ w.property.2)
  have h : (((Finset.univ : Finset X) \ y.val) ∩
      (Finset.univ \ z.val)).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card (hsub y) (hsub z) (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
        hsize, canonical_complement_card hsize y, canonical_complement_card hsize z]
      omega)
  apply intersect_of_core h
  · intro v hv
    exact Finset.mem_insert_of_mem hv
  · intro v hv
    exact Finset.mem_insert_of_mem hv

/-- Alon's construction is intersecting at every positive half-rank. -/
theorem canonical_intersecting (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    Intersecting (canonicalGadget m p).graph := by
  intro e he f hf
  rcases canonical_edge_cases he with ⟨a, ha, rfl⟩ | ⟨y, he⟩
  · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
    · exact canonical_core_core hsize ha hb
    · rcases hf with rfl | rfl
      · exact canonical_core_left hsize ha z
      · exact canonical_core_right hsize ha z
  · rcases he with rfl | rfl
    · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
      · simpa only [Finset.inter_comm] using canonical_core_left hsize hb y
      · rcases hf with rfl | rfl
        · exact canonical_left_left y z
        · exact canonical_left_right y z
    · rcases canonical_edge_cases hf with ⟨b, hb, rfl⟩ | ⟨z, hf⟩
      · simpa only [Finset.inter_comm] using canonical_core_right hsize hb y
      · rcases hf with rfl | rfl
        · simpa only [Finset.inter_comm] using canonical_left_right z y
        · exact canonical_right_right hm hsize y z

/-- Both colourability directions are included: the chromatic number is EXACTLY 3. -/
theorem canonical_threeChromatic (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    ThreeChromatic (canonicalGadget m p).graph := by
  exact ⟨threeColorable_of_intersecting (r := m + 1) (by omega)
      (canonical_uniform m p hsize) (canonical_intersecting hm hsize),
    canonical_not_twoColorable m p hsize⟩

/-- Every ambient vertex occurs in an edge. No isolated vertices pad the count. -/
theorem canonical_support_eq_univ (hm : 0 < m) (hsize : Fintype.card X = 2 * m) :
    support (canonicalGadget m p).graph = Finset.univ := by
  classical
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    change v ∈ (canonicalGadget m p).graph.biUnion id
    rcases v with x | y
    · obtain ⟨s, hxs, hsU, hscard⟩ :=
        Finset.exists_subsuperset_card_eq
          (s := {x}) (t := (Finset.univ : Finset X)) (n := m + 1)
          (Finset.subset_univ _) (by simp) (by
            rw [Finset.card_univ, hsize]
            omega)
      have hs : s ∈ (canonicalGadget m p).core :=
        Finset.mem_powersetCard.mpr ⟨hsU, hscard⟩
      refine Finset.mem_biUnion.mpr ⟨liftCore s, coreEdge_mem _ hs, ?_⟩
      exact (inl_mem_liftCore x s).mpr (hxs (Finset.mem_singleton_self x))
    · refine Finset.mem_biUnion.mpr
        ⟨leftEdge (canonicalGadget m p) y, leftEdge_mem _ y, ?_⟩
      exact Finset.mem_insert_self _ _

end Canonical
end JSP692
