import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace JSP000840

/-- The four vertices used in the finite specialization of the Rademacher theorem. -/
abbrev Vertex := Fin 4

/-- The six possible unordered edges on four labelled vertices. -/
abbrev Edge := Fin 6

/-- The endpoint set associated with each of the six possible edges. -/
def edgeVertices (e : Edge) : Finset Vertex :=
  match e with
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0, 3}
  | 3 => {1, 2}
  | 4 => {1, 3}
  | 5 => {2, 3}

/-- A simple graph is a finite set of the six possible edges. -/
abbrev Graph := Finset Edge

/-- The edges whose endpoints are contained in a vertex set. -/
def edgesWithin (t : Finset Vertex) : Finset Edge :=
  Finset.univ.filter (fun e => edgeVertices e ⊆ t)

/-- For four vertices, a triangle is identified by the unique omitted vertex. -/
def triangleVertices (omitted : Vertex) : Finset Vertex :=
  Finset.univ.erase omitted

/-- A computable Boolean test that all edges within a triangle occur in `G`. -/
def isTriangleBool (G : Graph) (omitted : Vertex) : Bool :=
  let t := triangleVertices omitted
  ((edgesWithin t).filter (fun e => e ∈ G)).card == (edgesWithin t).card

/-- The number of triangles in a graph, counted by their vertex sets. -/
def triangleCount (G : Graph) : Nat :=
  (Finset.univ.filter (fun omitted => isTriangleBool G omitted = true)).card

/--
The locked finite target: a simple graph on four vertices with five edges has at
least two triangles. This is the `n = 4`, `t = 1` specialization of the
Rademacher bound cited in the public source.
-/
def targetStatement : Prop :=
  ∀ G : Graph, G.card = 5 → 2 ≤ triangleCount G

end JSP000840
