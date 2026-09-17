import Mathlib

set_option autoImplicit false

open Finset

namespace JSP000840

/-- Rademacher's triangle supersaturation theorem for finite simple graphs. -/
def targetStatement : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj],
    (Fintype.card α) ^ 2 / 4 < #G.edgeFinset →
    Fintype.card α / 2 ≤ #(G.cliqueFinset 3)

end JSP000840
