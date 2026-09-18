import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.NormNum

namespace JSP000746

/-- Three distinct positive vertices in increasing Schur order, inside `[1,N]`. -/
def HasIndependentSchurTriple (G : SimpleGraph ℕ) (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b ≤ N ∧
    ¬G.Adj a b ∧ ¬G.Adj a (a + b) ∧ ¬G.Adj b (a + b)

/-- Any three mutual adjacencies contradict triangle-freeness. -/
lemma triangle_clause (G : SimpleGraph ℕ) (hG : G.CliqueFree 3) (a b c : ℕ) :
    G.Adj a b → G.Adj a c → G.Adj b c → False := by
  intro hab hac hbc
  exact hG {a,b,c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

/-- Failure to find the requested triple supplies each positive Schur clause. -/
lemma schur_clause (G : SimpleGraph ℕ) (N a b : ℕ)
    (h : ¬HasIndependentSchurTriple G N) (ha : 0 < a) (hab : a < b)
    (hN : a + b ≤ N) :
    ¬G.Adj a b → ¬G.Adj a (a+b) → ¬G.Adj b (a+b) → False := by
  intro h₁ h₂ h₃
  exact h ⟨a,b,ha,hab,hN,h₁,h₂,h₃⟩

lemma independent_triple (G : SimpleGraph ℕ) {a b c : ℕ}
    (hab : ¬G.Adj a b) (hac : ¬G.Adj a c) (hbc : ¬G.Adj b c) :
    G.IsIndepSet {a,b,c} := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact hab
  · exact hac
  · exact fun h => hab h.symm
  · exact False.elim (hxy rfl)
  · exact hbc
  · exact fun h => hac h.symm
  · exact fun h => hbc h.symm
  · exact False.elim (hxy rfl)

end JSP000746
