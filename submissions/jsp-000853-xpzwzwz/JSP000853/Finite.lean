import JSP000853.Definitions
import Mathlib.Data.Finset.Max

/-!
# Finite infrastructure for JSP-000853

Small lemmas used by both halves of the proof.  In particular, an admissible
pair mapping needs a deterministic fallback value whenever the geometric grid
construction degenerates.
-/

namespace JSP000853

section Fallback

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem exists_away_from_pair (hα : 2 < Fintype.card α) (x y : α) :
    ∃ z : α, z ≠ x ∧ z ≠ y := by
  classical
  by_contra h
  have hall : ∀ z : α, z = x ∨ z = y := by
    intro z
    by_contra hz
    exact h ⟨z, fun hzx => hz (Or.inl hzx), fun hzy => hz (Or.inr hzy)⟩
  have hsub : (Finset.univ : Finset α) ⊆ {x, y} := by
    intro z hz
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hall z
  have hcard : Fintype.card α ≤ 2 := by
    rw [← Finset.card_univ]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  exact (Nat.not_lt_of_ge hcard) hα

theorem pairComplement_nonempty (hα : 2 < Fintype.card α) (x y : α) :
    ((Finset.univ : Finset α) \ {x, y}).Nonempty := by
  obtain ⟨z, hzx, hzy⟩ := exists_away_from_pair hα x y
  exact ⟨z, by simp [hzx, hzy]⟩

/-- A canonical element outside `{x,y}`.  Defining it through the complement
finset makes symmetry in `x,y` provable, unlike an unconstrained use of
`Classical.choose` on two merely equivalent propositions. -/
noncomputable def fallbackPoint (hα : 2 < Fintype.card α) (x y : α) : α :=
  ((Finset.univ : Finset α) \ {x, y}).min' (pairComplement_nonempty hα x y)

theorem fallbackPoint_mem (hα : 2 < Fintype.card α) (x y : α) :
    fallbackPoint hα x y ∈ (Finset.univ : Finset α) \ {x, y} :=
  Finset.min'_mem _ _

theorem fallbackPoint_ne_left (hα : 2 < Fintype.card α) (x y : α) :
    fallbackPoint hα x y ≠ x := by
  have h := (Finset.mem_sdiff.mp (fallbackPoint_mem hα x y)).2
  intro heq
  exact h (by simp [heq])

theorem fallbackPoint_ne_right (hα : 2 < Fintype.card α) (x y : α) :
    fallbackPoint hα x y ≠ y := by
  have h := (Finset.mem_sdiff.mp (fallbackPoint_mem hα x y)).2
  intro heq
  exact h (by simp [heq])

theorem fallbackPoint_comm (hα : 2 < Fintype.card α) (x y : α) :
    fallbackPoint hα x y = fallbackPoint hα y x := by
  unfold fallbackPoint
  have hpair : ({x, y} : Finset α) = {y, x} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact or_comm
  apply le_antisymm
  · apply Finset.min'_le
    rw [hpair]
    exact Finset.min'_mem _ _
  · apply Finset.min'_le
    rw [← hpair]
    exact Finset.min'_mem _ _

end Fallback

namespace PairMapping

/-- Transport a pair mapping backwards along an equivalence. -/
def reindex (e : α ≃ β) (f : PairMapping β) : PairMapping α where
  toFun x y := e.symm (f (e x) (e y))
  map_symm x y := by simp only [f.map_symm]
  map_ne_left := by
    intro x y hxy hbad
    have himage := congrArg e hbad
    simp only [Equiv.apply_symm_apply] at himage
    exact f.map_ne_left (e.injective.ne hxy) himage
  map_ne_right := by
    intro x y hxy hbad
    have himage := congrArg e hbad
    simp only [Equiv.apply_symm_apply] at himage
    exact f.map_ne_right (e.injective.ne hxy) himage

section Restrict

variable [Fintype α] [LinearOrder α]

/-- Pull a pair mapping back along an embedding.  When the ambient image leaves
the embedded copy, use the canonical third point as a fallback. -/
noncomputable def restrict (hα : 2 < Fintype.card α) (e : α ↪ β)
    (f : PairMapping β) : PairMapping α := by
  classical
  refine
    { toFun := fun x y ↦
        if h : ∃ z, e z = f (e x) (e y) then Classical.choose h
        else fallbackPoint hα x y
      map_symm := ?_
      map_ne_left := ?_
      map_ne_right := ?_ }
  · intro x y
    rw [f.map_symm (e y) (e x)]
    by_cases h : ∃ z, e z = f (e x) (e y)
    · simp [h]
    · simp [h, fallbackPoint_comm]
  · intro x y hxy
    split
    · rename_i h
      intro heq
      apply f.map_ne_left (e.injective.ne hxy)
      rw [← Classical.choose_spec h, heq]
    · exact fallbackPoint_ne_left hα x y
  · intro x y hxy
    split
    · rename_i h
      intro heq
      apply f.map_ne_right (e.injective.ne hxy)
      rw [← Classical.choose_spec h, heq]
    · exact fallbackPoint_ne_right hα x y

/-- A free set for the restricted mapping remains free after embedding into
the ambient mapping. -/
theorem isFree_image_of_restrict_isFree (hα : 2 < Fintype.card α)
    [DecidableEq β] (e : α ↪ β) (f : PairMapping β) {S : Finset α}
    (hfree : (restrict hα e f).IsFree S) : f.IsFree (S.image e) := by
  classical
  intro ex hex ey hey hxy hmem
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hex
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hey
  obtain ⟨z, hz, hzimage⟩ := Finset.mem_image.mp hmem
  have hxy' : x ≠ y := fun h ↦ hxy (by simp [h])
  have hrange : ∃ w, e w = f (e x) (e y) := ⟨z, hzimage⟩
  apply hfree hx hy hxy'
  have hrestrict : restrict hα e f x y = z := by
    simp only [restrict, hrange, dite_true]
    apply e.injective
    exact (Classical.choose_spec hrange).trans hzimage.symm
  rwa [hrestrict]

end Restrict

end PairMapping

end JSP000853
