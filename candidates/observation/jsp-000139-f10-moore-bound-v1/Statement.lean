import Mathlib

open scoped BigOperators

namespace JSP000139

/-- A finite simple graph presented as an irreflexive symmetric adjacency relation. -/
structure SimpleGraphOn (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ {u v : V}, Adj u v → Adj v u
  loopless : ∀ v : V, ¬ Adj v v

/-- The finite neighbor set of a vertex. -/
noncomputable def neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

/-- Vertex degree. -/
noncomputable def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V) (v : V) : ℕ :=
  (neighbors G v).card

/-- Triangle-freeness, retained from the source problem statement. -/
def TriangleFree {V : Type*} (G : SimpleGraphOn V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → G.Adj c a → False

/-- Every vertex is at graph distance at most two from `root`, written with paths
of length zero, one, or two. -/
def WithinTwoFrom {V : Type*} (G : SimpleGraphOn V) (root : V) : Prop :=
  ∀ x : V, x = root ∨ G.Adj root x ∨ ∃ y : V, G.Adj root y ∧ G.Adj y x

/-- The exact Moore-bound statement used below.  It is the elementary lower-bound
component of the triangle-free diameter-two problem: if all degrees are at most
`D`, then the graph has at most `D^2 + 1` vertices. -/
def MooreBoundStatement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraphOn V) : Prop :=
  ∀ D : ℕ,
    (∀ v : V, degree G v ≤ D) →
    (∀ root : V, WithinTwoFrom G root) →
    Fintype.card V ≤ D ^ 2 + 1

end JSP000139
