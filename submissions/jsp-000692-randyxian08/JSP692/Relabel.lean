import JSP692.Hypergraph

set_option autoImplicit false

/-! Transport to Fin n without changing edges, colours, or vertex coverage. -/
namespace JSP692

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def relabel (e : V ≃ W) (H : Hypergraph V) : Hypergraph W :=
  H.image (fun a => a.image e)

theorem uniform_relabel (e : V ≃ W) {H : Hypergraph V} {r : ℕ}
    (hu : Uniform H r) : Uniform (relabel e H) r := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.card_image_of_injective b e.injective, hu b hb]

theorem intersecting_relabel (e : V ≃ W) {H : Hypergraph V}
    (hi : Intersecting H) : Intersecting (relabel e H) := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨x, hx⟩ := hi a' ha' b' hb'
  exact ⟨e x, Finset.mem_inter.mpr
    ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩,
     Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩⟩⟩

theorem proper_relabel_iff {C : Type*} (e : V ≃ W)
    (H : Hypergraph V) (c : W → C) :
    Proper (relabel e H) c ↔ Proper H (fun v => c (e v)) := by
  constructor
  · intro h a ha
    have hamem : a.image e ∈ relabel e H := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨u, hu, v, hv, hne⟩ := h (a.image e) hamem
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨x, hx, y, hy, hne⟩
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, hx, y, hy, hne⟩ := h b hb
    exact ⟨e x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      e y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hne⟩

theorem threeChromatic_relabel (e : V ≃ W) {H : Hypergraph V}
    (h : ThreeChromatic H) : ThreeChromatic (relabel e H) := by
  constructor
  · obtain ⟨c, hc⟩ := h.1
    refine ⟨fun w => c (e.symm w), (proper_relabel_iff e H _).mpr ?_⟩
    simpa only [Equiv.symm_apply_apply] using hc
  · rintro ⟨c, hc⟩
    exact h.2 ⟨fun v => c (e v), (proper_relabel_iff e H c).mp hc⟩

theorem support_relabel_eq_univ [Fintype V] [Fintype W]
    (e : V ≃ W) {H : Hypergraph V} (h : support H = Finset.univ) :
    support (relabel e H) = Finset.univ := by
  classical
  ext w
  constructor
  · intro _
    exact Finset.mem_univ w
  · intro _
    have hx : e.symm w ∈ support H := by rw [h]; exact Finset.mem_univ _
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr
      ⟨a.image e, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨e.symm w, hxa, e.apply_symm_apply w⟩

end JSP692
