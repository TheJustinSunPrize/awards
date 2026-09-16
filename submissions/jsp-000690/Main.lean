import Std

/-!
JSP-000690, chromatic interpretation of Erdos Problem 834.
Independent formalization of Ruiliang Li's explicit construction,
arXiv:2512.24850v1, Theorem 4.1 and Appendix A (2025).
No claim of a new mathematical construction or of award eligibility.

Vertices are 0,...,8, corresponding to vertices 1,...,9 in the paper.
Edges are strictly increasing triples; this is a canonical representation
of three-element subsets, not a multihypergraph or a strong colouring.
-/

namespace JSP690

abbrev Edge (n : Nat) := Fin n × Fin n × Fin n
abbrev Hypergraph (n : Nat) := List (Edge n)

def Uniform {n : Nat} (H : Hypergraph n) : Prop :=
  ∀ e ∈ H, e.1 < e.2.1 ∧ e.2.1 < e.2.2

def Simple {n : Nat} (H : Hypergraph n) : Prop := H.Nodup

def Proper {n : Nat} {C : Type} (H : Hypergraph n) (c : Fin n → C) : Prop :=
  ∀ e ∈ H, c e.1 ≠ c e.2.1 ∨ c e.1 ≠ c e.2.2

def Colorable {n : Nat} (H : Hypergraph n) (k : Nat) : Prop :=
  ∃ c : Fin n → Fin k, Proper H c

def Degree {n : Nat} (H : Hypergraph n) (v : Fin n) : Nat :=
  (H.filter fun e => v == e.1 || v == e.2.1 || v == e.2.2).length

def DeleteEdge {n : Nat} (H : Hypergraph n) (e : Edge n) : Hypergraph n :=
  H.filter (fun f => f != e)

-- The removed vertex remains as an isolated ambient label. Restricting any
-- proper colouring to the remaining labels gives exactly the usual deletion.
def DeleteVertex {n : Nat} (H : Hypergraph n) (v : Fin n) : Hypergraph n :=
  H.filter (fun e => v != e.1 && v != e.2.1 && v != e.2.2)

def Critical3 {n : Nat} (H : Hypergraph n) : Prop :=
  Colorable H 3 ∧ ¬ Colorable H 2 ∧
  (∀ e ∈ H, Colorable (DeleteEdge H e) 2) ∧
  (∀ v, Colorable (DeleteVertex H v) 2)

def exampleGraph : Hypergraph 9 :=
  [(0,1,2), (0,1,8), (0,2,7), (0,3,5), (0,3,7), (0,3,8),
   (0,4,6), (0,4,7), (0,4,8), (0,5,6), (1,2,5), (1,2,6),
   (1,3,8), (1,4,8), (1,5,6), (2,3,7), (2,4,7), (2,5,6),
   (3,5,7), (3,5,8), (4,6,7), (4,6,8)]

theorem uniform : Uniform exampleGraph := by unfold Uniform; decide
theorem simple : Simple exampleGraph := by unfold Simple; decide
theorem edge_count : exampleGraph.length = 22 := by decide
theorem minimum_degree : ∀ v : Fin 9, 7 ≤ Degree exampleGraph v := by decide
theorem degree_seven : Degree exampleGraph 1 = 7 := by decide

def coloring (a b c d e f g h i : Fin 2) (v : Fin 9) : Fin 2 :=
  match v.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e
  | 5 => f | 6 => g | 7 => h | _ => i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_two_certificate : ∀ a b c d e f g h i : Fin 2,
    ¬ Proper exampleGraph (coloring a b c d e f g h i) := by unfold Proper; decide

theorem coloring_complete (c : Fin 9 → Fin 2) :
    coloring (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) = c := by
  funext v
  match v with
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl | ⟨8, _⟩ => rfl

theorem not_two_colorable : ¬ Colorable exampleGraph 2 := by
  intro ⟨c, hc⟩
  have h := no_two_certificate (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8)
  rw [coloring_complete c] at h
  exact h hc

def threeColoring (v : Fin 9) : Fin 3 :=
  match v.val with
  | 2 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | _ => 0

theorem three_colorable : Colorable exampleGraph 3 :=
  ⟨threeColoring, by unfold Proper; decide⟩

def maskColoring (mask : Nat) (v : Fin 9) : Fin 2 :=
  if mask.testBit v.val then 1 else 0

-- Independently regenerated witnesses, checked below by kernel reduction.
def edgeMask (e : Edge 9) : Nat :=
  match e.1.val, e.2.1.val, e.2.2.val with
  | 0,1,2 => 31 | 0,1,8 => 60 | 0,2,7 => 58
  | 0,3,5 => 59 | 0,3,7 => 203 | 0,3,8 => 178
  | 0,4,6 => 91 | 0,4,7 => 179 | 0,4,8 => 202
  | 0,5,6 => 30 | 1,2,5 => 62 | 1,2,6 => 94
  | 1,3,8 => 53 | 1,4,8 => 77 | 1,5,6 => 29
  | 2,3,7 => 51 | 2,4,7 => 75 | 2,5,6 => 27
  | 3,5,7 => 186 | 3,5,8 => 195 | 4,6,7 => 218
  | 4,6,8 => 163 | _,_,_ => 0

theorem edge_certificates : ∀ e ∈ exampleGraph,
    Proper (DeleteEdge exampleGraph e) (maskColoring (edgeMask e)) := by
  unfold Proper
  decide

theorem edge_critical : ∀ e ∈ exampleGraph, Colorable (DeleteEdge exampleGraph e) 2 :=
  fun e he => ⟨maskColoring (edgeMask e), edge_certificates e he⟩

def vertexMask (v : Fin 9) : Nat :=
  match v.val with
  | 0 => 30 | 1 => 29 | 2 => 27 | 3 => 51 | 4 => 75
  | 5 => 27 | 6 => 27 | 7 => 51 | _ => 53

theorem vertex_certificates : ∀ v : Fin 9,
    Proper (DeleteVertex exampleGraph v) (maskColoring (vertexMask v)) := by
  unfold Proper
  decide

theorem vertex_critical : ∀ v, Colorable (DeleteVertex exampleGraph v) 2 :=
  fun v => ⟨maskColoring (vertexMask v), vertex_certificates v⟩

theorem colorable_mono {n a b : Nat} {H : Hypergraph n}
    (hab : a ≤ b) (h : Colorable H a) : Colorable H b := by
  rcases h with ⟨c, hc⟩
  refine ⟨fun v => (c v).castLE hab, ?_⟩
  intro e he
  rcases hc e he with h | h
  · left
    intro eq
    apply h
    apply Fin.ext
    exact congrArg (fun x : Fin b => x.val) eq
  · right
    intro eq
    apply h
    apply Fin.ext
    exact congrArg (fun x : Fin b => x.val) eq

theorem no_fewer_colors (k : Nat) (hk : k < 3) : ¬ Colorable exampleGraph k := by
  intro h
  exact not_two_colorable (colorable_mono (by omega) h)

theorem proper_mono {n : Nat} {C : Type} {H G : Hypergraph n} {c : Fin n → C}
    (h : Proper H c) (hsub : ∀ e ∈ G, e ∈ H) : Proper G c :=
  fun e he => h e (hsub e he)

-- All strict edge subhypergraphs, not just single-edge deletions.
theorem proper_subgraph_colorable (G : Hypergraph 9)
    (hsub : ∀ e ∈ G, e ∈ exampleGraph)
    (hstrict : ∃ e ∈ exampleGraph, e ∉ G) : Colorable G 2 := by
  rcases hstrict with ⟨e, he, hnot⟩
  rcases edge_critical e he with ⟨c, hc⟩
  refine ⟨c, proper_mono hc ?_⟩
  intro f hf
  apply List.mem_filter.mpr
  refine ⟨hsub f hf, ?_⟩
  have hne : f ≠ e := by
    intro eq
    exact hnot (eq ▸ hf)
  simpa only [bne_iff_ne] using hne

def Incident {n : Nat} (v : Fin n) (e : Edge n) : Prop :=
  v = e.1 ∨ v = e.2.1 ∨ v = e.2.2

/-- The compact predicate is equivalent to the usual no-monochromatic-edge
definition: every edge contains two vertices of different colours. -/
theorem proper_iff_nonmonochromatic {n : Nat} {C : Type}
    (H : Hypergraph n) (c : Fin n → C) :
    Proper H c ↔ ∀ e ∈ H, ∃ u v, Incident u e ∧ Incident v e ∧ c u ≠ c v := by
  constructor
  · intro hc e he
    rcases hc e he with h | h
    · exact ⟨e.1, e.2.1, Or.inl rfl, Or.inr (Or.inl rfl), h⟩
    · exact ⟨e.1, e.2.2, Or.inl rfl, Or.inr (Or.inr rfl), h⟩
  · intro hc e he
    classical
    by_cases h12 : c e.1 = c e.2.1
    · by_cases h13 : c e.1 = c e.2.2
      · rcases hc e he with ⟨u, v, hu, hv, hne⟩
        rcases hu with rfl | rfl | rfl <;>
          rcases hv with rfl | rfl | rfl <;> simp_all
      · exact Or.inr h13
    · exact Or.inl h12

/-- The deletion certificate restricts to the actual vertex complement. -/
theorem vertex_deletion_restricted (v : Fin 9) :
    ∃ c : {w : Fin 9 // w ≠ v} → Fin 2,
      ∀ a b d : {w : Fin 9 // w ≠ v},
        (a.val, b.val, d.val) ∈ exampleGraph → c a ≠ c b ∨ c a ≠ c d := by
  rcases vertex_critical v with ⟨c, hc⟩
  refine ⟨fun w => c w.val, ?_⟩
  intro a b d he
  apply hc (a.val, b.val, d.val)
  apply List.mem_filter.mpr
  refine ⟨he, ?_⟩
  simp [Ne.symm a.property, Ne.symm b.property, Ne.symm d.property]

theorem not_one_of_nonempty {n : Nat} {H : Hypergraph n}
    (hn : 0 < H.length) : ¬ Colorable H 1 := by
  intro ⟨c, hc⟩
  obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp hn
  have hab : c e.1 = c e.2.1 := Fin.ext (by omega)
  have hac : c e.1 = c e.2.2 := Fin.ext (by omega)
  rcases hc e he with h | h
  · exact h hab
  · exact h hac

theorem edge_deletions_nonempty : ∀ e ∈ exampleGraph,
    0 < (DeleteEdge exampleGraph e).length := by decide

theorem vertex_deletions_nonempty : ∀ v : Fin 9,
    0 < (DeleteVertex exampleGraph v).length := by decide

theorem deletion_chromatic_number_two :
    (∀ e ∈ exampleGraph, Colorable (DeleteEdge exampleGraph e) 2 ∧
      ¬ Colorable (DeleteEdge exampleGraph e) 1) ∧
    (∀ v, Colorable (DeleteVertex exampleGraph v) 2 ∧
      ¬ Colorable (DeleteVertex exampleGraph v) 1) :=
  ⟨fun e he => ⟨edge_critical e he, not_one_of_nonempty (edge_deletions_nonempty e he)⟩,
   fun v => ⟨vertex_critical v, not_one_of_nonempty (vertex_deletions_nonempty v)⟩⟩

theorem critical : Critical3 exampleGraph :=
  ⟨three_colorable, not_two_colorable, edge_critical, vertex_critical⟩

/-- An affirmative answer to precisely the chromatic catalog question. -/
theorem jsp_000690 : ∃ (n : Nat) (H : Hypergraph n),
    Uniform H ∧ Simple H ∧ Critical3 H ∧ (∀ v, 7 ≤ Degree H v) :=
  ⟨9, exampleGraph, uniform, simple, critical, minimum_degree⟩

#print axioms jsp_000690
#print axioms no_fewer_colors
#print axioms proper_subgraph_colorable
#print axioms proper_iff_nonmonochromatic
#print axioms vertex_deletion_restricted
#print axioms deletion_chromatic_number_two

end JSP690
