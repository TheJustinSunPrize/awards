import JSP690.Definitions

/-!
Literal vertex subsets and arbitrary proper subhypergraphs.

The ambient bit-vector type remains fixed, while a colouring on `V` has the
literal domain `{v // V v}`. Strictness refers to an omitted edge or vertex,
never to the ordering of an edge list.
-/

namespace JSP690

/-- A weak colouring whose domain is exactly the specified vertex subset. -/
def ColorableOn {n : Nat} (H : Hypergraph n) (V : Vertex n → Prop)
    (k : Nat) : Prop :=
  ∃ c : {v : Vertex n // V v} → Fin k, ProperColoringOn H V c

/-- Every edge of `F` belongs to `H`, and all its vertices belong to `V`. -/
def SubgraphOn {n : Nat} (F H : Hypergraph n) (V : Vertex n → Prop) : Prop :=
  (∀ e ∈ F, e ∈ H) ∧ ∀ e ∈ F, ∀ v ∈ edgeVertices e, V v

/-- A genuine proper subhypergraph may omit an edge, a vertex, or both. -/
def StrictSubgraphOn {n : Nat} (F H : Hypergraph n)
    (V : Vertex n → Prop) : Prop :=
  SubgraphOn F H V ∧ ((∃ e ∈ H, e ∉ F) ∨ ∃ v : Vertex n, ¬ V v)

/-- Chromatic criticality for all genuine proper subhypergraphs, allowing
deletion of edges, vertices, or both. The colouring domain is literally `V`. -/
def ChromaticCritical {n : Nat} (H : Hypergraph n) (k : Nat) : Prop :=
  HasChromaticNumber H k ∧
    ∀ (F : Hypergraph n) (V : Vertex n → Prop),
      StrictSubgraphOn F H V → ColorableOn F V (k - 1)

theorem colorableOn_of_colorable {n k : Nat} {H : Hypergraph n}
    {V : Vertex n → Prop}
    (hV : ∀ e ∈ H, ∀ v ∈ edgeVertices e, V v) (h : Colorable H k) :
    ColorableOn H V k := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun v => c v.val, properColoring_restrict hV hc⟩

/-- Extend a colouring by assigning colour zero outside its original domain.
The positive-palette hypothesis is necessary for this literal extension. -/
theorem colorable_of_colorableOn {n k : Nat} {H : Hypergraph n}
    {V : Vertex n → Prop} [DecidablePred V]
    (hk : 0 < k) (h : ColorableOn H V k) : Colorable H k := by
  obtain ⟨c, hc⟩ := h
  let extended : Vertex n → Fin k := fun v =>
    if hv : V v then c ⟨v, hv⟩ else ⟨0, hk⟩
  refine ⟨extended, ?_⟩
  intro e he
  obtain ⟨u, v, hu, hv, hne⟩ := hc e he
  refine ⟨u.val, hu, v.val, hv, ?_⟩
  simpa [extended, u.property, v.property] using hne

theorem colorableOn_iff_colorable {n k : Nat} {H : Hypergraph n}
    {V : Vertex n → Prop} [DecidablePred V]
    (hk : 0 < k) (hV : ∀ e ∈ H, ∀ v ∈ edgeVertices e, V v) :
    ColorableOn H V k ↔ Colorable H k := by
  exact ⟨colorable_of_colorableOn hk, colorableOn_of_colorable hV⟩

/-- Vertex deletion discards every incident edge; it does not shorten edges. -/
theorem deleteVertex_vertices {n : Nat} (H : Hypergraph n)
    (deleted : Vertex n) :
    ∀ e ∈ deleteVertex H deleted, ∀ v ∈ edgeVertices e, v ≠ deleted := by
  intro e he v hv hsame
  subst v
  have hbit : e.getLsbD deleted.val = true := (mem_edgeVertices e deleted).mp hv
  have hnot : e ∉ deleteVertex H deleted := by
    simp [deleteVertex, hbit]
  exact hnot he

theorem colorableOn_deleteVertex {n k : Nat} {H : Hypergraph n}
    {deleted : Vertex n} (h : Colorable (deleteVertex H deleted) k) :
    ColorableOn (deleteVertex H deleted) (fun v => v ≠ deleted) k := by
  exact colorableOn_of_colorable (deleteVertex_vertices H deleted) h

/-- For a nonempty palette, the unused ambient coordinate and the literal
deleted-vertex domain give exactly the same colourability statement. -/
theorem colorableOn_deleteVertex_iff {n k : Nat} (H : Hypergraph n)
    (deleted : Vertex n) (hk : 0 < k) :
    ColorableOn (deleteVertex H deleted) (fun v => v ≠ deleted) k ↔
      Colorable (deleteVertex H deleted) k := by
  exact colorableOn_iff_colorable hk (deleteVertex_vertices H deleted)

theorem subgraphOn_subset_deleteVertex {n : Nat} {F H : Hypergraph n}
    {V : Vertex n → Prop} (hsub : SubgraphOn F H V)
    {deleted : Vertex n} (hdeleted : ¬ V deleted) :
    ∀ e ∈ F, e ∈ deleteVertex H deleted := by
  intro e he
  have hbit : e.getLsbD deleted.val = false := by
    cases hb : e.getLsbD deleted.val with
    | false => rfl
    | true =>
      exact False.elim
        (hdeleted (hsub.2 e he deleted ((mem_edgeVertices e deleted).mpr hb)))
  apply List.mem_filter.mpr
  refine ⟨hsub.1 e he, ?_⟩
  change (!e.getLsbD deleted.val) = true
  rw [hbit]
  rfl

/-- All single-edge and single-vertex deletions being colourable suffices for
every proper subhypergraph, with its own literal vertex domain, to be colourable.
No non-isolation assumption is needed because both deletion families are given. -/
theorem strictSubgraphOn_colorable_of_deletions {n k : Nat}
    {H : Hypergraph n}
    (hedge : ∀ e ∈ H, Colorable (deleteEdge H e) k)
    (hvertex : ∀ v : Vertex n, Colorable (deleteVertex H v) k)
    {F : Hypergraph n} {V : Vertex n → Prop}
    (hF : StrictSubgraphOn F H V) : ColorableOn F V k := by
  obtain ⟨hsub, hstrict⟩ := hF
  apply colorableOn_of_colorable hsub.2
  cases hstrict with
  | inl hmissing =>
    exact properSubhypergraph_colorable_of_edge_deletions hedge ⟨hsub.1, hmissing⟩
  | inr hmissing =>
    obtain ⟨v, hv⟩ := hmissing
    exact colorable_mono (subgraphOn_subset_deleteVertex hsub hv) (hvertex v)

end JSP690
