import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordinary four-cycle packings

Related to Erdős problem 577 and JSP-000467. Cycles are not required to be
induced. One injection records all vertices, including disjointness between
different cycles. The graph is Mathlib's complete bipartite graph.
-/

namespace BipartiteC4

open Finset

abbrev Vertex (a b : ℕ) := Fin a ⊕ Fin b

abbrev graph (a b : ℕ) : SimpleGraph (Vertex a b) :=
  completeBipartiteGraph (Fin a) (Fin b)

instance (a b : ℕ) : DecidableRel (graph a b).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∨ _ ∧ _))

/-- A genuine family of vertex-disjoint ordinary four-cycles. -/
structure Packing {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  vertices : Fin k × Fin 4 ↪ V
  adjacent : ∀ i j, G.Adj (vertices (i,j)) (vertices (i,j+1))

def HasPacking {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (Packing G k)

/-- The cyclic adjacency condition is exactly adjacency in Mathlib's C4. -/
lemma cycle_adj (i j : Fin 4) :
    (SimpleGraph.cycleGraph 4).Adj i j ↔ i = j + 1 ∨ j = i + 1 := by
  rw [SimpleGraph.cycleGraph_adj]
  simp only [sub_eq_iff_eq_add']

/-- Every member is an injective graph copy of Mathlib's four-cycle. -/
def Packing.cycle {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (p : Packing G k) (i : Fin k) : (SimpleGraph.cycleGraph 4).Copy G where
  toHom := {
    toFun := fun j => p.vertices (i,j)
    map_rel' := by
      intro j l h
      rcases (cycle_adj j l).mp h with h | h
      · subst j
        exact (p.adjacent i l).symm
      · subst l
        exact p.adjacent i j }
  injective' := fun _ _ h => (Prod.mk.inj (p.vertices.injective h)).2

theorem Packing.disjoint_cycles {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (p : Packing G k) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (Set.range (p.cycle i)) (Set.range (p.cycle j)) := by
  rw [Set.disjoint_left]
  rintro v ⟨x,hx⟩ ⟨y,hy⟩
  exact hij (Prod.mk.inj (p.vertices.injective (hx.trans hy.symm))).1

/-- Exchanging the two bipartition classes preserves every packing. -/
def Packing.swap {a b k : ℕ} (p : Packing (graph a b) k) :
    Packing (graph b a) k where
  vertices := p.vertices.trans (Equiv.sumComm (Fin a) (Fin b)).toEmbedding
  adjacent i j := by
    have h := p.adjacent i j
    change (graph b a).Adj (Sum.swap _) (Sum.swap _)
    cases hx : p.vertices (i,j) <;> cases hy : p.vertices (i,j+1) <;>
      simp_all [graph, completeBipartiteGraph]

end BipartiteC4
