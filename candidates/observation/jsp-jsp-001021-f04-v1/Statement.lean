import Mathlib

set_option autoImplicit false

namespace JSP001021

/-- A tournament is an orientation of every pair of distinct vertices. -/
structure Tournament (α : Type*) [DecidableEq α] where
  edge : α → α → Prop
  complete : ∀ ⦃a b : α⦄, a ≠ b → edge a b ∨ edge b a
  antisymm : ∀ ⦃a b : α⦄, edge a b → ¬ edge b a
  edge_decidable : DecidableRel edge

instance {α : Type*} [DecidableEq α] (T : Tournament α) : DecidableRel T.edge :=
  T.edge_decidable

/-- An ordered injective copy of a transitive subtournament. -/
def TransitiveEmbedding {α : Type*} [DecidableEq α]
    (T : Tournament α) (k : Nat) (f : Fin k → α) : Prop :=
  Function.Injective f ∧
    ∀ ⦃i j : Fin k⦄, i < j → T.edge (f i) (f j)

/--
The elementary Erdős--Moser lower-bound theorem, reindexed so that a tournament
with `2 ^ k` vertices is shown to contain a transitive subtournament with `k + 1`
vertices.  This is the exact statement formalized by `Proof.lean`.
-/
def JSP001021Statement : Prop :=
  ∀ (k : Nat),
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α),
      Fintype.card α = 2 ^ k →
        ∃ f : Fin (k + 1) → α, TransitiveEmbedding T (k + 1) f

end JSP001021
