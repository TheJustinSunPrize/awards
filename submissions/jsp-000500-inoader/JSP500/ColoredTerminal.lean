import JSP500.ColorCounting
import JSP500.TerminalCore
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]

lemma edges_add_complement (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    induction e using Sym2.inductionOn with
    | _ u v =>
      have h1' : G.Adj u v := by simpa using h1
      have h2' : u ≠ v ∧ ¬G.Adj u v := by simpa using h2
      exact h2'.2 h1'
  have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, SimpleGraph.top_adj]
      exact ⟨fun h => h.elim (fun h => h.ne) And.left,
        fun h => (Classical.em (G.Adj u v)).elim Or.inl (fun hn => Or.inr ⟨h,hn⟩)⟩
  rw [← Finset.card_union_of_disjoint hd, hu]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma balanced_color_edges_at_least_seven (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : Fintype.card V = 14) (k : Fin 7) : 7 ≤ (colorGraph c k).edgeFinset.card := by
  have ht := (balanced_compl_cliqueFree c hb k).card_edgeFinset_le
  have hsum := edges_add_complement (colorGraph c k)
  rw [hn] at ht hsum
  norm_num [SimpleGraph.turanNumber_eq, Nat.choose_two_right] at ht hsum
  omega

/-- The terminal obstruction for an actual balanced seven-coloring on
fourteen vertices. -/
theorem no_colored_terminal_fourteen (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : Fintype.card V = 14) (k : Fin 7)
    (halpha : (colorGraph c k)ᶜ.CliqueFree 3)
    (homega : (colorGraph c k).CliqueFree 7) : False := by
  have hsum := sum_edgesOn c Finset.univ
  simp only [edgesOn_univ, Finset.card_univ, hn] at hsum
  norm_num [Nat.choose_two_right] at hsum
  have hk : k ∈ (Finset.univ : Finset (Fin 7)) := Finset.mem_univ k
  rw [← Finset.sum_erase_add _ _ hk] at hsum
  have hrest : 42 ≤ ∑ j ∈ Finset.univ.erase k, (colorGraph c j).edgeFinset.card := by
    calc
      42 = ∑ _j ∈ (Finset.univ : Finset (Fin 7)).erase k, 7 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => balanced_color_edges_at_least_seven c hb hn j)
  have hp := edges_add_complement (colorGraph c k)
  rw [hn] at hp
  norm_num [Nat.choose_two_right] at hp
  exact terminal_core_fourteen (colorGraph c k)ᶜ hn halpha (by simpa using homega) (by omega)

end JSP500
