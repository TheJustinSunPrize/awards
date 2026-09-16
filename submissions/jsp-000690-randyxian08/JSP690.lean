import Std

/-!
# JSP-000690: a 3-uniform, 3-chromatic-critical hypergraph of minimum degree 7

The explicit witness and deletion certificates are from Ruiliang Li,
"On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7",
arXiv:2512.24850v1, Theorem 4.1 and Appendices A and B.

This development uses only Lean's standard library. An edge is its strictly
increasing triple of vertices. Thus edge equality is equality of 3-element
sets, not equality of arbitrary ordered triples; `Edge.ext_vertices` proves
this representation property. A simple hypergraph is a duplicate-free list
of such edges. Colors are weak colors: an edge must not be monochromatic.

Vertices 0,...,8 in Lean correspond to vertices 1,...,9 in the paper.
The finite proof scripts use kernel reduction (`decide`).
Locally compiled and axiom-audited with official Lean 4.19.0 on 2026-09-16.
See verification/status.json for the source-bound receipt and REVIEW.md
for the two compatibility fixes, statement review, and verification limits.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP690

/-- A canonical representation of a three-element subset of `Fin n`. -/
structure Edge (n : Nat) where
  a : Fin n
  b : Fin n
  c : Fin n
  ab : a.val < b.val
  bc : b.val < c.val
  deriving DecidableEq

namespace Edge

def Incident {n : Nat} (e : Edge n) (v : Fin n) : Prop :=
  v = e.a ∨ v = e.b ∨ v = e.c

instance {n : Nat} (e : Edge n) (v : Fin n) :
    Decidable (e.Incident v) := by
  unfold Incident
  infer_instance

def vertices {n : Nat} (e : Edge n) : List (Fin n) := [e.a, e.b, e.c]

theorem vertices_length {n : Nat} (e : Edge n) : e.vertices.length = 3 := rfl

theorem vertices_nodup {n : Nat} (e : Edge n) : e.vertices.Nodup := by
  have hab : e.a ≠ e.b := by
    intro h
    have heq := congrArg Fin.val h
    have hlt := e.ab
    omega
  have hbc : e.b ≠ e.c := by
    intro h
    have heq := congrArg Fin.val h
    have hlt := e.bc
    omega
  have hac : e.a ≠ e.c := by
    intro h
    have heq := congrArg Fin.val h
    have h₁ := e.ab
    have h₂ := e.bc
    omega
  simp [vertices, hab, hbc, hac]

theorem mem_vertices {n : Nat} (e : Edge n) (v : Fin n) :
    v ∈ e.vertices ↔ e.Incident v := by
  simp [vertices, Incident]

/-- Different canonical edges cannot represent the same vertex set. -/
theorem ext_vertices {n : Nat} {e f : Edge n}
    (h : ∀ v, e.Incident v ↔ f.Incident v) : e = f := by
  have ha := (h e.a).mp (Or.inl rfl)
  have hb := (h e.b).mp (Or.inr (Or.inl rfl))
  have hc := (h e.c).mp (Or.inr (Or.inr rfl))
  have hfa := (h f.a).mpr (Or.inl rfl)
  have hfc := (h f.c).mpr (Or.inr (Or.inr rfl))
  have eab := e.ab
  have ebc := e.bc
  have fab := f.ab
  have fbc := f.bc
  simp only [Incident] at ha hb hc hfa hfc
  have hav : e.a.val = f.a.val := by
    rcases ha with ha | ha | ha <;>
      rcases hfa with hfa | hfa | hfa <;>
      have haa := congrArg Fin.val ha <;>
      have hff := congrArg Fin.val hfa <;> omega
  have hcv : e.c.val = f.c.val := by
    rcases hc with hc | hc | hc <;>
      rcases hfc with hfc | hfc | hfc <;>
      have hcc := congrArg Fin.val hc <;>
      have hff := congrArg Fin.val hfc <;> omega
  have hbv : e.b.val = f.b.val := by
    rcases hb with hb | hb | hb <;>
      have hbb := congrArg Fin.val hb <;> omega
  have haeq : e.a = f.a := Fin.ext hav
  have hbeq : e.b = f.b := Fin.ext hbv
  have hceq : e.c = f.c := Fin.ext hcv
  cases e
  cases f
  cases haeq
  cases hbeq
  cases hceq
  rfl

/-- Weak properness: at least one vertex differs in color from the first. -/
def Proper {n : Nat} {C : Type} (e : Edge n) (color : Fin n → C) : Prop :=
  color e.a ≠ color e.b ∨ color e.a ≠ color e.c

instance {n : Nat} {C : Type} [DecidableEq C]
    (e : Edge n) (color : Fin n → C) : Decidable (e.Proper color) := by
  unfold Proper
  infer_instance

/-- The triple definition is exactly non-monochromaticity on the vertex set. -/
theorem proper_iff_nonmonochromatic {n : Nat} {C : Type}
    (e : Edge n) (color : Fin n → C) :
    e.Proper color ↔
      ∃ u v, e.Incident u ∧ e.Incident v ∧ color u ≠ color v := by
  classical
  constructor
  · intro h
    cases h with
    | inl hab => exact ⟨e.a, e.b, Or.inl rfl, Or.inr (Or.inl rfl), hab⟩
    | inr hac => exact ⟨e.a, e.c, Or.inl rfl, Or.inr (Or.inr rfl), hac⟩
  · rintro ⟨u, v, hu, hv, hne⟩
    by_cases hab : color e.a = color e.b
    · by_cases hac : color e.a = color e.c
      · have hu' : color u = color e.a := by
          rcases hu with h | h | h
          · exact congrArg color h
          · exact (congrArg color h).trans hab.symm
          · exact (congrArg color h).trans hac.symm
        have hv' : color v = color e.a := by
          rcases hv with h | h | h
          · exact congrArg color h
          · exact (congrArg color h).trans hab.symm
          · exact (congrArg color h).trans hac.symm
        exact False.elim (hne (hu'.trans hv'.symm))
      · exact Or.inr hac
    · exact Or.inl hab

end Edge

/-- A simple three-uniform hypergraph on the vertex set `Fin n`. -/
structure SimpleThreeGraph (n : Nat) where
  edges : List (Edge n)
  nodup : edges.Nodup

/-- Every edge must be weakly properly colored. -/
def Proper {n : Nat} {C : Type} (es : List (Edge n)) (color : Fin n → C) : Prop :=
  ∀ e ∈ es, e.Proper color

instance {n : Nat} {C : Type} [DecidableEq C]
    (es : List (Edge n)) (color : Fin n → C) : Decidable (Proper es color) := by
  unfold Proper
  infer_instance

def Colorable {n : Nat} (es : List (Edge n)) (k : Nat) : Prop :=
  ∃ color : Fin n → Fin k, Proper es color

def HasChromaticNumber {n : Nat} (es : List (Edge n)) (k : Nat) : Prop :=
  Colorable es k ∧ ∀ q : Nat, q < k → ¬ Colorable es q

def degree {n : Nat} (H : SimpleThreeGraph n) (v : Fin n) : Nat :=
  (H.edges.filter (fun e => decide (e.Incident v))).length

/-- Deleting a vertex removes its entire incident edges; edges are not shrunk. -/
def deleteVertex {n : Nat} (es : List (Edge n)) (v : Fin n) : List (Edge n) :=
  es.filter (fun e => !decide (e.Incident v))

def EdgeCritical {n : Nat} (H : SimpleThreeGraph n) : Prop :=
  ∀ e ∈ H.edges, Colorable (H.edges.erase e) 2

def VertexCritical {n : Nat} (H : SimpleThreeGraph n) : Prop :=
  ∀ v : Fin n, Colorable (deleteVertex H.edges v) 2

/-- The usual three-chromatic criticality, with both deletion properties. -/
def ThreeChromaticCritical {n : Nat} (H : SimpleThreeGraph n) : Prop :=
  HasChromaticNumber H.edges 3 ∧ EdgeCritical H ∧ VertexCritical H

theorem proper_mono {n : Nat} {C : Type} {es fs : List (Edge n)}
    {color : Fin n → C} (hsub : ∀ e ∈ es, e ∈ fs)
    (h : Proper fs color) : Proper es color := by
  intro e he
  exact h e (hsub e he)

/-- Recoloring by an injective map preserves weak properness. -/
theorem proper_map {n : Nat} {C D : Type} {es : List (Edge n)}
    {color : Fin n → C} (f : C → D)
    (hf : ∀ x y, f x = f y → x = y) (h : Proper es color) :
    Proper es (fun v => f (color v)) := by
  intro e he
  cases h e he with
  | inl hab => exact Or.inl (fun hEq => hab (hf _ _ hEq))
  | inr hac => exact Or.inr (fun hEq => hac (hf _ _ hEq))

theorem colorable_mono {n q k : Nat} {es : List (Edge n)}
    (hqk : q ≤ k) (h : Colorable es q) : Colorable es k := by
  rcases h with ⟨color, hcolor⟩
  let f : Fin q → Fin k := fun x => ⟨x.val, Nat.lt_of_lt_of_le x.isLt hqk⟩
  refine ⟨fun v => f (color v), proper_map f ?_ hcolor⟩
  intro x y hxy
  exact Fin.ext (congrArg (fun z : Fin k => z.val) hxy)

/-- A subhypergraph has an actual subset of vertices and a subset of edges.
Every surviving edge must be wholly contained in its vertex set. -/
structure Subhypergraph {n : Nat} (G : SimpleThreeGraph n) where
  vertex : Fin n → Prop
  edges : List (Edge n)
  nodup : edges.Nodup
  edges_sub : ∀ e ∈ edges, e ∈ G.edges
  edge_vertices : ∀ e ∈ edges, vertex e.a ∧ vertex e.b ∧ vertex e.c

namespace Subhypergraph

/-- Properness of the subhypergraph ignores list order: a vertex or edge is missing. -/
def IsProper {n : Nat} {G : SimpleThreeGraph n} (S : Subhypergraph G) : Prop :=
  (∃ v, ¬ S.vertex v) ∨ (∃ e, e ∈ G.edges ∧ e ∉ S.edges)

/-- Colors are assigned only to the vertices that actually survive. -/
def Colorable {n : Nat} {G : SimpleThreeGraph n}
    (S : Subhypergraph G) (k : Nat) : Prop :=
  ∃ color : {v : Fin n // S.vertex v} → Fin k,
    ∀ (e : Edge n) (he : e ∈ S.edges),
      color ⟨e.a, (S.edge_vertices e he).1⟩ ≠
        color ⟨e.b, (S.edge_vertices e he).2.1⟩ ∨
      color ⟨e.a, (S.edge_vertices e he).1⟩ ≠
        color ⟨e.c, (S.edge_vertices e he).2.2⟩

/-- A global coloring restricts to the genuine vertex set of a subhypergraph. -/
theorem restrict_coloring {n k : Nat} {G : SimpleThreeGraph n}
    (S : Subhypergraph G) (h : JSP690.Colorable S.edges k) : S.Colorable k := by
  rcases h with ⟨color, hcolor⟩
  exact ⟨fun v => color v.val, fun e he => hcolor e he⟩

end Subhypergraph

/-- The two single-deletion conditions imply the usual full criticality property:
every proper subhypergraph is two-colorable. This is a general lemma, not a
finite test of a preselected list of subhypergraphs. -/
theorem proper_subhypergraph_two_colorable {n : Nat} {G : SimpleThreeGraph n}
    (hec : EdgeCritical G) (hvc : VertexCritical G)
    (S : Subhypergraph G) (hp : S.IsProper) : S.Colorable 2 := by
  apply S.restrict_coloring
  rcases hp with ⟨v, hv⟩ | ⟨e, he, hmissing⟩
  · rcases hvc v with ⟨color, hcolor⟩
    refine ⟨color, proper_mono ?_ hcolor⟩
    intro f hf
    have havoid : ¬ f.Incident v := by
      intro hinc
      rcases hinc with h | h | h
      · exact hv (h.symm ▸ (S.edge_vertices f hf).1)
      · exact hv (h.symm ▸ (S.edge_vertices f hf).2.1)
      · exact hv (h.symm ▸ (S.edge_vertices f hf).2.2)
    simpa [deleteVertex, havoid] using S.edges_sub f hf
  · rcases hec e he with ⟨color, hcolor⟩
    refine ⟨color, proper_mono ?_ hcolor⟩
    intro f hf
    have hfe : f ≠ e := by
      intro h
      exact hmissing (h ▸ hf)
    exact (List.mem_erase_of_ne hfe).mpr (S.edges_sub f hf)

-- The explicit 22-edge witness, in the order of equation (5) in the paper.
def edges : List (Edge 9) := [
  ⟨0, 1, 2, by decide, by decide⟩,
  ⟨0, 1, 8, by decide, by decide⟩,
  ⟨0, 2, 7, by decide, by decide⟩,
  ⟨0, 3, 5, by decide, by decide⟩,
  ⟨0, 3, 7, by decide, by decide⟩,
  ⟨0, 3, 8, by decide, by decide⟩,
  ⟨0, 4, 6, by decide, by decide⟩,
  ⟨0, 4, 7, by decide, by decide⟩,
  ⟨0, 4, 8, by decide, by decide⟩,
  ⟨0, 5, 6, by decide, by decide⟩,
  ⟨1, 2, 5, by decide, by decide⟩,
  ⟨1, 2, 6, by decide, by decide⟩,
  ⟨1, 3, 8, by decide, by decide⟩,
  ⟨1, 4, 8, by decide, by decide⟩,
  ⟨1, 5, 6, by decide, by decide⟩,
  ⟨2, 3, 7, by decide, by decide⟩,
  ⟨2, 4, 7, by decide, by decide⟩,
  ⟨2, 5, 6, by decide, by decide⟩,
  ⟨3, 5, 7, by decide, by decide⟩,
  ⟨3, 5, 8, by decide, by decide⟩,
  ⟨4, 6, 7, by decide, by decide⟩,
  ⟨4, 6, 8, by decide, by decide⟩
]

def H : SimpleThreeGraph 9 := ⟨edges, by decide⟩

theorem edge_count : H.edges.length = 22 := by decide

theorem degree_sequence :
    (List.finRange 9).map (degree H) = [10, 7, 7, 7, 7, 7, 7, 7, 7] := by
  decide

theorem minimum_degree_at_least_seven : ∀ v : Fin 9, 7 ≤ degree H v := by
  decide

-- A closed, finite assertion: all 2^9 assignments of two colors are excluded.
-- Applying it to the nine values of an arbitrary function loses no colorings.
-- The nested finite quantifiers and conjunction exceed the default instance size.
set_option synthInstance.maxSize 1024 in
private theorem binary_obstruction :
    ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 : Fin 2,
    ¬ (
      (x0 ≠ x1 ∨ x0 ≠ x2) ∧
      (x0 ≠ x1 ∨ x0 ≠ x8) ∧
      (x0 ≠ x2 ∨ x0 ≠ x7) ∧
      (x0 ≠ x3 ∨ x0 ≠ x5) ∧
      (x0 ≠ x3 ∨ x0 ≠ x7) ∧
      (x0 ≠ x3 ∨ x0 ≠ x8) ∧
      (x0 ≠ x4 ∨ x0 ≠ x6) ∧
      (x0 ≠ x4 ∨ x0 ≠ x7) ∧
      (x0 ≠ x4 ∨ x0 ≠ x8) ∧
      (x0 ≠ x5 ∨ x0 ≠ x6) ∧
      (x1 ≠ x2 ∨ x1 ≠ x5) ∧
      (x1 ≠ x2 ∨ x1 ≠ x6) ∧
      (x1 ≠ x3 ∨ x1 ≠ x8) ∧
      (x1 ≠ x4 ∨ x1 ≠ x8) ∧
      (x1 ≠ x5 ∨ x1 ≠ x6) ∧
      (x2 ≠ x3 ∨ x2 ≠ x7) ∧
      (x2 ≠ x4 ∨ x2 ≠ x7) ∧
      (x2 ≠ x5 ∨ x2 ≠ x6) ∧
      (x3 ≠ x5 ∨ x3 ≠ x7) ∧
      (x3 ≠ x5 ∨ x3 ≠ x8) ∧
      (x4 ≠ x6 ∨ x4 ≠ x7) ∧
      (x4 ≠ x6 ∨ x4 ≠ x8)) := by
  decide

theorem not_two_colorable : ¬ Colorable H.edges 2 := by
  rintro ⟨color, hcolor⟩
  have h := binary_obstruction
    (color 0) (color 1) (color 2) (color 3) (color 4)
    (color 5) (color 6) (color 7) (color 8)
  apply h
  simpa [Proper, Edge.Proper, H, edges] using hcolor

def threeColor (v : Fin 9) : Fin 3 :=
  match v.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | _ => 1

theorem three_colorable : Colorable H.edges 3 :=
  ⟨threeColor, by decide⟩

theorem chromatic_number_three : HasChromaticNumber H.edges 3 := by
  refine ⟨three_colorable, ?_⟩
  intro q hq hcolor
  have hq2 : q ≤ 2 := by omega
  exact not_two_colorable (colorable_mono hq2 hcolor)

/-- Blue sets for each deleted edge. The default is irrelevant off the witness. -/
def edgeBlue (e : Edge 9) : List (Fin 9) :=
  match e.a.val, e.b.val, e.c.val with
  | 0, 1, 2 => [5, 6, 7, 8]
  | 0, 1, 8 => [2, 3, 4, 5]
  | 0, 2, 7 => [1, 3, 4, 5]
  | 0, 3, 5 => [1, 6, 7, 8]
  | 0, 3, 7 => [2, 4, 5, 8]
  | 0, 3, 8 => [1, 4, 5, 7]
  | 0, 4, 6 => [1, 5, 7, 8]
  | 0, 4, 7 => [2, 3, 6, 8]
  | 0, 4, 8 => [1, 3, 6, 7]
  | 0, 5, 6 => [1, 2, 3, 4]
  | 1, 2, 5 => [0, 6, 7, 8]
  | 1, 2, 6 => [0, 5, 7, 8]
  | 1, 3, 8 => [0, 2, 4, 5]
  | 1, 4, 8 => [0, 2, 3, 6]
  | 1, 5, 6 => [0, 2, 3, 4]
  | 2, 3, 7 => [0, 1, 4, 5]
  | 2, 4, 7 => [0, 1, 3, 6]
  | 2, 5, 6 => [0, 1, 3, 4]
  | 3, 5, 7 => [0, 2, 6, 8]
  | 3, 5, 8 => [0, 1, 6, 7]
  | 4, 6, 7 => [0, 2, 5, 8]
  | 4, 6, 8 => [0, 1, 5, 7]
  | _, _, _ => []

def blueColor (blue : List (Fin 9)) (v : Fin 9) : Fin 2 :=
  if v ∈ blue then 1 else 0

/-- Every listed certificate is checked, for every surviving edge. -/
theorem edge_deletion_certificates :
    ∀ e ∈ H.edges, Proper (H.edges.erase e) (blueColor (edgeBlue e)) := by
  decide

theorem edge_critical : EdgeCritical H := by
  intro e he
  exact ⟨blueColor (edgeBlue e), edge_deletion_certificates e he⟩

/-- Blue sets for each deleted vertex. -/
def vertexBlue (v : Fin 9) : List (Fin 9) :=
  match v.val with
  | 0 => [1, 2, 3, 4]
  | 1 => [0, 2, 3, 4]
  | 2 => [0, 1, 3, 4]
  | 3 => [0, 1, 4, 5]
  | 4 => [0, 1, 3, 6]
  | 5 => [0, 1, 3, 4]
  | 6 => [0, 1, 3, 4]
  | 7 => [0, 1, 3, 6]
  | _ => [0, 1, 5, 7]

theorem vertex_deletion_certificates :
    ∀ v : Fin 9, Proper (deleteVertex H.edges v) (blueColor (vertexBlue v)) := by
  decide

theorem vertex_critical : VertexCritical H := by
  intro v
  exact ⟨blueColor (vertexBlue v), vertex_deletion_certificates v⟩

theorem H_critical : ThreeChromaticCritical H :=
  ⟨chromatic_number_three, edge_critical, vertex_critical⟩

/-- Every edge is genuinely a three-element subset, with no repeated vertex. -/
theorem H_three_uniform :
    ∀ e ∈ H.edges, e.vertices.length = 3 ∧ e.vertices.Nodup := by
  intro e _
  exact ⟨e.vertices_length, e.vertices_nodup⟩

theorem minimum_degree_exactly_seven :
    (∀ v : Fin 9, 7 ≤ degree H v) ∧ (∃ v : Fin 9, degree H v = 7) :=
  ⟨minimum_degree_at_least_seven, 1, by decide⟩

theorem H_all_proper_subhypergraphs :
    ∀ S : Subhypergraph H, S.IsProper → S.Colorable 2 :=
  proper_subhypergraph_two_colorable edge_critical vertex_critical

/-- Existence theorem answering JSP-000690 affirmatively. -/
theorem JSP_000690 :
    ∃ G : SimpleThreeGraph 9,
      G.edges.length = 22 ∧
      ThreeChromaticCritical G ∧
      (∀ v : Fin 9, 7 ≤ degree G v) :=
  ⟨H, edge_count, H_critical, minimum_degree_at_least_seven⟩

/-- A strengthened statement using actual vertex subsets for all subhypergraphs. -/
theorem JSP_000690_full :
    ∃ G : SimpleThreeGraph 9,
      G.edges.length = 22 ∧
      HasChromaticNumber G.edges 3 ∧
      (∀ S : Subhypergraph G, S.IsProper → S.Colorable 2) ∧
      (∀ v : Fin 9, 7 ≤ degree G v) ∧
      (∃ v : Fin 9, degree G v = 7) :=
  ⟨H, edge_count, chromatic_number_three, H_all_proper_subhypergraphs,
    minimum_degree_exactly_seven⟩

#print axioms JSP_000690
#print axioms JSP_000690_full
#print axioms Edge.ext_vertices
#print axioms Edge.proper_iff_nonmonochromatic

end JSP690
