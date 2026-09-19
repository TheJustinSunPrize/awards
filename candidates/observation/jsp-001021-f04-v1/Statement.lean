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

/-- The finite type of all ordered transitive copies of size `k`.  In a tournament
such an ordering is the unique ordering of its vertex set, so its cardinality is
also the number of transitive `k`-subtournaments. -/
abbrev EmbeddingType {α : Type*} [DecidableEq α]
    (T : Tournament α) (k : Nat) :=
  {f : Fin k → α // TransitiveEmbedding T k f}

noncomputable instance embeddingTypeFintype {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) : Fintype (EmbeddingType T k) :=
  Fintype.ofFinite _

/-- `r_T(k)`, the number of ordered transitive `k`-subtournaments of `T`. -/
noncomputable def embeddingCount {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) : Nat :=
  Fintype.card (EmbeddingType T k)

/-- Moon's lower-bound function.  The strict source condition
`n > 2^m - 1` is equivalent to `2^m ≤ n`. -/
noncomputable def moonTau (n k : Nat) : ℝ :=
  match k with
  | 0 => 1
  | m + 1 =>
      if 2 ^ m ≤ n then
        ∏ i ∈ Finset.range (m + 1),
          ((n : ℝ) - ((2 : ℝ)^i - 1)) / (2 : ℝ)^i
      else 0

/-- Moon's source-faithful all-quantifier lower-bound statement: every finite
 tournament of order `n` has at least `τ(n,k)` transitive `k`-subtournaments. -/
def JSP001021Statement : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat),
    moonTau (Fintype.card α) k ≤ (embeddingCount T k : ℝ)

end JSP001021
