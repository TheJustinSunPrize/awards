import Std

/-!
Finite simple hypergraphs, represented without external mathematical libraries.
An `Edge n` is its characteristic bit vector on `Fin n`: ordering and repeated
vertices cannot change an edge. A graph is an edge list, required to be `Nodup`.
All colourings below quantify over actual functions on the vertex type.
-/

namespace JSP690

abbrev Vertex (n : Nat) := Fin n
abbrev Edge (n : Nat) := BitVec n
abbrev Hypergraph (n : Nat) := List (Edge n)

def edgeVertices {n : Nat} (e : Edge n) : List (Vertex n) :=
  (List.finRange n).filter (fun v => e.getLsbD v.val)

theorem mem_edgeVertices {n : Nat} (e : Edge n) (v : Vertex n) :
    v ∈ edgeVertices e ↔ e.getLsbD v.val = true := by
  simp [edgeVertices, List.mem_finRange]

def Simple {n : Nat} (H : Hypergraph n) : Prop := H.Nodup

def Uniform {n : Nat} (H : Hypergraph n) (r : Nat) : Prop :=
  ∀ e ∈ H, (edgeVertices e).length = r

instance {n : Nat} (H : Hypergraph n) (r : Nat) : Decidable (Uniform H r) :=
  inferInstanceAs (Decidable (∀ e ∈ H, (edgeVertices e).length = r))

def degree {n : Nat} (H : Hypergraph n) (v : Vertex n) : Nat :=
  H.countP (fun e => e.getLsbD v.val)

/-- Weak hypergraph colouring: every hyperedge contains differently coloured vertices. -/
def ProperColoring {n : Nat} {α : Type} (H : Hypergraph n) (c : Vertex n → α) : Prop :=
  ∀ e ∈ H, ∃ u ∈ edgeVertices e, ∃ v ∈ edgeVertices e, c u ≠ c v

instance {n : Nat} {α : Type} [DecidableEq α] (H : Hypergraph n)
    (c : Vertex n → α) : Decidable (ProperColoring H c) :=
  inferInstanceAs
    (Decidable (∀ e ∈ H, ∃ u ∈ edgeVertices e, ∃ v ∈ edgeVertices e, c u ≠ c v))

def Colorable {n : Nat} (H : Hypergraph n) (k : Nat) : Prop :=
  ∃ c : Vertex n → Fin k, ProperColoring H c

def HasChromaticNumber {n : Nat} (H : Hypergraph n) (k : Nat) : Prop :=
  Colorable H k ∧ ∀ j : Nat, j < k → ¬ Colorable H j

def deleteEdge {n : Nat} (H : Hypergraph n) (e : Edge n) : Hypergraph n :=
  H.filter (fun f => f != e)

/-- Delete a vertex and every incident edge. The deleted vertex is an unused
coordinate of a colouring; `ProperColoringOn` below gives the literal restricted domain. -/
def deleteVertex {n : Nat} (H : Hypergraph n) (v : Vertex n) : Hypergraph n :=
  H.filter (fun e => !e.getLsbD v.val)

/-- Strict inclusion of edge SETS, not inequality or ordering of their lists. -/
def ProperSubhypergraph {n : Nat} (F H : Hypergraph n) : Prop :=
  (∀ e ∈ F, e ∈ H) ∧ ∃ e ∈ H, e ∉ F

/-- Criticality under deletion of edges, with the ambient vertex set fixed.
The full vertex-and-edge notion `ChromaticCritical` is defined in `Subgraph`. -/
def EdgeChromaticCritical {n : Nat} (H : Hypergraph n) (k : Nat) : Prop :=
  HasChromaticNumber H k ∧
    ∀ F : Hypergraph n, ProperSubhypergraph F H → Colorable F (k - 1)

theorem properColoring_mono {n : Nat} {α : Type} {F H : Hypergraph n}
    {c : Vertex n → α} (hsub : ∀ e ∈ F, e ∈ H) (hc : ProperColoring H c) :
    ProperColoring F c := by
  intro e he
  exact hc e (hsub e he)

theorem colorable_mono {n k : Nat} {F H : Hypergraph n}
    (hsub : ∀ e ∈ F, e ∈ H) (h : Colorable H k) : Colorable F k := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, properColoring_mono hsub hc⟩

theorem properSubhypergraph_colorable_of_edge_deletions {n k : Nat}
    {H : Hypergraph n} (hdel : ∀ e ∈ H, Colorable (deleteEdge H e) k)
    {F : Hypergraph n} (hF : ProperSubhypergraph F H) : Colorable F k := by
  obtain ⟨hsub, e, he, hnot⟩ := hF
  apply colorable_mono (H := deleteEdge H e) ?_ (hdel e he)
  intro f hf
  have hne : f ≠ e := by
    intro h
    apply hnot
    simpa [h] using hf
  simp [deleteEdge, hsub f hf, hne]

/-- A colouring whose function domain literally is a specified vertex subset. -/
def ProperColoringOn {n : Nat} {α : Type} (H : Hypergraph n)
    (V : Vertex n → Prop) (c : {v : Vertex n // V v} → α) : Prop :=
  ∀ e ∈ H, ∃ u : {v : Vertex n // V v}, ∃ v : {v : Vertex n // V v},
    u.val ∈ edgeVertices e ∧ v.val ∈ edgeVertices e ∧ c u ≠ c v

theorem properColoring_restrict {n : Nat} {α : Type} {H : Hypergraph n}
    {V : Vertex n → Prop} {c : Vertex n → α}
    (hV : ∀ e ∈ H, ∀ v ∈ edgeVertices e, V v) (hc : ProperColoring H c) :
    ProperColoringOn H V (fun v => c v.val) := by
  intro e he
  obtain ⟨u, hu, v, hv, hne⟩ := hc e he
  exact ⟨⟨u, hV e he u hu⟩, ⟨v, hV e he v hv⟩, hu, hv, hne⟩

end JSP690
