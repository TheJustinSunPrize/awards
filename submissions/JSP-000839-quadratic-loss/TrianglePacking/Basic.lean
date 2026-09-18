import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Graphs and edge-disjoint triangle packings

The graph has two independent classes of size `r` and a complete core of size `s`.
All pairs from different classes are adjacent. This generalizes the four-vertex
core in Sauer's construction recorded at https://www.erdosproblems.com/1009.
-/

namespace TrianglePacking

abbrev Vertex (r s : ℕ) := (Fin r ⊕ Fin r) ⊕ Fin s

def part {r s : ℕ} : Vertex r s → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def graph (r s : ℕ) : SimpleGraph (Vertex r s) where
  Adj v w := v ≠ w ∧ (part v ≠ part w ∨ part v = 2)
  symm := by
    constructor
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h
    · exact Or.inl h.symm
    · by_cases hp : part w = 2
      · exact Or.inr hp
      · exact Or.inl (by simpa [h] using hp)
  loopless := ⟨by simp⟩

instance (r s : ℕ) : DecidableRel (graph r s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ≠ _ ∨ _ = (2 : Fin 3))))

/-- Oriented copies of the edges spanned by a finite vertex set. -/
def arcs {V : Type*} [DecidableEq V] (T : Finset V) : Finset (V × V) := T.offDiag

/-- Distinct triangles may share vertices, but may not share an edge. -/
def IsPacking {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (P : Finset (Finset V)) : Prop :=
  (∀ T ∈ P, G.IsNClique 3 T) ∧
    (P : Set (Finset V)).Pairwise (fun T U => Disjoint (arcs T) (arcs U))

/-- Nonnegative integer weights on oriented edges. -/
def weight {r s : ℕ} (e : Vertex r s × Vertex r s) : ℕ :=
  if part e.1 = 2 then (if part e.2 = 2 then 2 else 3)
  else (if part e.2 = 2 then 3 else 0)

end TrianglePacking
