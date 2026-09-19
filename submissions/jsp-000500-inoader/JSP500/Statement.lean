import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Sym.Sym2

/-!
The exact fixed-r=7 target for JSP-000500 / Erdos Problem 617.
This module states the target as a definition. It does not assert a proof.
-/

namespace JSP500

def Misses {V : Type} (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k

def Balanced {V : Type} (c : Sym2 V → Fin 7) : Prop :=
  ∀ S : Finset V, S.card = 8 → ∀ k : Fin 7, ¬ Misses c S k

def Main : Prop :=
  ∀ c : Sym2 (Fin 50) → Fin 7,
    ∃ S : Finset (Fin 50), S.card = 8 ∧ ∃ k : Fin 7, Misses c S k

def Upstream : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 50 →
    ∀ c : Sym2 V → Fin 7,
      ∃ S : Finset V, S.card = 8 ∧ ∃ k : Fin 7, Misses c S k

theorem main_iff_no_balanced : Main ↔ ∀ c : Sym2 (Fin 50) → Fin 7, ¬ Balanced c := by
  classical
  simp only [Main, Balanced, not_forall, not_not, exists_prop]

end JSP500
