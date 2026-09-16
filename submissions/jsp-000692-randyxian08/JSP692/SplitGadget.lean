import JSP692.Hypergraph

set_option autoImplicit false

/-!
A generic reduction from all vertex colorings to colorings of the core only.
No conclusion about an infinite family is inferred from a finite test.
Authoring status: NOT COMPILED in this environment.
-/

namespace JSP692

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype Y]

structure SplitGadget (X Y : Type*) where
  core : Finset (Finset X)
  left : Y → Finset X
  right : Y → Finset X

def liftCore (s : Finset X) : Finset (X ⊕ Y) := s.image Sum.inl

def leftEdge (d : SplitGadget X Y) (y : Y) : Finset (X ⊕ Y) :=
  insert (Sum.inr y) (liftCore (d.left y))

def rightEdge (d : SplitGadget X Y) (y : Y) : Finset (X ⊕ Y) :=
  insert (Sum.inr y) (liftCore (d.right y))

def SplitGadget.graph (d : SplitGadget X Y) : Hypergraph (X ⊕ Y) :=
  d.core.image liftCore ∪ Finset.univ.biUnion (fun y => {leftEdge d y, rightEdge d y})

/-- Every core coloring either contains a monochromatic core edge, or has
oppositely monochromatic halves at some split vertex. -/
def SplitGadget.CoreObstructs (d : SplitGadget X Y) : Prop :=
  ∀ c : X → Bool,
    (∃ e ∈ d.core, Mono e c) ∨
    ∃ y : Y, ∃ b : Bool,
      (∀ x ∈ d.left y, c x = b) ∧
      (∀ x ∈ d.right y, c x = !b)

theorem coreEdge_mem (d : SplitGadget X Y) {e : Finset X} (he : e ∈ d.core) :
    liftCore e ∈ d.graph := by
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem leftEdge_mem (d : SplitGadget X Y) (y : Y) : leftEdge d y ∈ d.graph := by
  apply Finset.mem_union.mpr
  apply Or.inr
  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by simp⟩

theorem rightEdge_mem (d : SplitGadget X Y) (y : Y) : rightEdge d y ∈ d.graph := by
  apply Finset.mem_union.mpr
  apply Or.inr
  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, by simp⟩

theorem mono_liftCore {C : Type*} {s : Finset X} {c : X ⊕ Y → C}
    (h : Mono s (fun x => c (Sum.inl x))) : Mono (liftCore s) c := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  exact hb x hx

theorem mono_insert_liftCore {C : Type*} {s : Finset X} {c : X ⊕ Y → C}
    {y : Y} {b : C} (hy : c (Sum.inr y) = b)
    (hs : ∀ x ∈ s, c (Sum.inl x) = b) :
    Mono (insert (Sum.inr y) (liftCore s)) c := by
  refine ⟨b, ?_⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with hv | hv
  · simpa [hv] using hy
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hs x hx

/-- This is the soundness theorem used for the reduced finite certificates. -/
theorem not_twoColorable_of_coreObstructs (d : SplitGadget X Y)
    (hd : d.CoreObstructs) : ¬ ∃ c : X ⊕ Y → Bool, Proper d.graph c := by
  classical
  rintro ⟨c, hc⟩
  rcases hd (fun x => c (Sum.inl x)) with hcore | hsplit
  · obtain ⟨e, he, hm⟩ := hcore
    exact not_proper_of_mono (coreEdge_mem d he) (mono_liftCore hm) hc
  · obtain ⟨y, b, hleft, hright⟩ := hsplit
    have hcolor : c (Sum.inr y) = b ∨ c (Sum.inr y) = !b := by
      cases b <;> cases c (Sum.inr y) <;> simp
    rcases hcolor with hcolor | hcolor
    · exact not_proper_of_mono (leftEdge_mem d y)
        (mono_insert_liftCore hcolor hleft) hc
    · exact not_proper_of_mono (rightEdge_mem d y)
        (mono_insert_liftCore hcolor hright) hc

end JSP692
