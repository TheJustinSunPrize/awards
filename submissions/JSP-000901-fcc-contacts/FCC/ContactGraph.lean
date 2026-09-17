import FCC.Padding
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace FCC

open Finset

/-- The actual undirected unit-distance contact graph of the FCC points. -/
noncomputable def contactGraph (m : ℕ) : SimpleGraph (Vertex m) where
  Adj u v := dist (point u) (point v) = 1
  symm.symm u v h := by simpa only [dist_comm] using h
  loopless.irrefl u := by simp

instance (m : ℕ) : DecidableRel (contactGraph m).Adj := fun u v =>
  decidable_of_iff (Contact u v) (point_dist_eq_one_iff u v).symm

theorem contactGraph_adj_iff {m : ℕ} (u v : Vertex m) :
    (contactGraph m).Adj u v ↔ Contact u v := point_dist_eq_one_iff u v

theorem Contact.symm {m : ℕ} {u v : Vertex m} (h : Contact u v) : Contact v u := by
  rw [← point_dist_eq_one_iff, dist_comm, point_dist_eq_one_iff]
  exact h

/-- Ordering the distinct parity classes gives each unordered contact a unique
representative, and omits no edge of the genuine Euclidean contact graph. -/
theorem contactGraph_edgeFinset_eq (m : ℕ) :
    (contactGraph m).edgeFinset =
      (contactPairs m).image (fun p => s(p.1, p.2)) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, contactGraph_adj_iff]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h.offset_ne with hlt | hlt
      · exact mem_image.mpr ⟨(u,v), by simp [contactPairs, hlt, h], rfl⟩
      · exact mem_image.mpr ⟨(v,u), by simp [contactPairs, hlt, h.symm], Sym2.eq_swap⟩
    · intro h
      obtain ⟨⟨a,b⟩, hab, he⟩ := mem_image.mp h
      have hc : Contact a b := (mem_filter.mp hab).2.2
      change s(a,b) = s(u,v) at he
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hc
      · exact hc.symm

/-- The canonical orientation is injective on contacts, so unordered edges
are counted once, rather than twice as directed pairs. -/
theorem contactPairs_sym2_injOn (m : ℕ) :
    Set.InjOn (fun p : Vertex m × Vertex m => s(p.1,p.2)) (contactPairs m) := by
  intro x hx y hy he
  have hxlt := (mem_filter.mp hx).2.1
  have hylt := (mem_filter.mp hy).2.1
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext h1 h2
  · rw [h1,h2] at hxlt
    exact False.elim (lt_asymm hxlt hylt)

theorem contactGraph_edge_card (m : ℕ) :
    (contactGraph m).edgeFinset.card = (contactPairs m).card := by
  rw [contactGraph_edgeFinset_eq]
  exact card_image_of_injOn (contactPairs_sym2_injOn m)

/-- The genuine Euclidean unit-distance graph after adding isolated points. -/
noncomputable def paddedContactGraph (m q : ℕ) :
    SimpleGraph (Vertex m ⊕ Fin q) where
  Adj u v := dist (paddedPoint u) (paddedPoint v) = 1
  symm.symm u v h := by simpa only [dist_comm] using h
  loopless.irrefl u := by simp

noncomputable instance (m q : ℕ) : DecidableRel (paddedContactGraph m q).Adj := by
  classical
  exact fun _ _ => inferInstance

/-- The extra vertices are isolated; the map is an equality of actual graphs,
not merely an equality of specially defined pair counters. -/
theorem paddedContactGraph_eq_map (m q : ℕ) :
    paddedContactGraph m q =
      (contactGraph m).map (Function.Embedding.inl : Vertex m ↪ Vertex m ⊕ Fin q) := by
  ext u v
  rw [SimpleGraph.map_adj]
  change (dist (paddedPoint u) (paddedPoint v) = 1) ↔ _
  rw [paddedPoint_contact_iff]
  constructor
  · rintro ⟨a,b,rfl,rfl,h⟩
    exact ⟨a,b,(contactGraph_adj_iff a b).mpr h,rfl,rfl⟩
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨a,b,ha.symm,hb.symm,(contactGraph_adj_iff a b).mp h⟩

theorem paddedContactGraph_edgeFinset_eq (m q : ℕ) :
    (paddedContactGraph m q).edgeFinset = (contactPairs m).image
      (fun p => s((Sum.inl p.1 : Vertex m ⊕ Fin q), Sum.inl p.2)) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (dist (paddedPoint u) (paddedPoint v) = 1) ↔ _
    rw [paddedPoint_contact_iff]
    constructor
    · rintro ⟨a,b,rfl,rfl,h⟩
      rcases lt_or_gt_of_ne h.offset_ne with hlt | hlt
      · exact mem_image.mpr ⟨(a,b), by simp [contactPairs, hlt, h], rfl⟩
      · exact mem_image.mpr ⟨(b,a), by simp [contactPairs, hlt, h.symm], Sym2.eq_swap⟩
    · intro h
      obtain ⟨⟨a,b⟩, hab, he⟩ := mem_image.mp h
      have hc : Contact a b := (mem_filter.mp hab).2.2
      change s((Sum.inl a : Vertex m ⊕ Fin q), Sum.inl b) = s(u,v) at he
      rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact ⟨a,b,ha.symm,hb.symm,hc⟩
      · exact ⟨b,a,hb.symm,ha.symm,hc.symm⟩

theorem paddedContactGraph_edge_card (m q : ℕ) :
    (paddedContactGraph m q).edgeFinset.card = (contactPairs m).card := by
  rw [paddedContactGraph_edgeFinset_eq]
  apply card_image_of_injOn
  intro x hx y hy he
  have hxlt := (mem_filter.mp hx).2.1
  have hylt := (mem_filter.mp hy).2.1
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext (Sum.inl.inj h1) (Sum.inl.inj h2)
  · have h1' := Sum.inl.inj h1
    have h2' := Sum.inl.inj h2
    rw [h1',h2'] at hxlt
    exact False.elim (lt_asymm hxlt hylt)

end FCC
