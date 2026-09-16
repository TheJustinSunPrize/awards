import JSP500.Statement
import JSP500.Brooks
import Mathlib.Data.Sym.Card

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph formed by the edges of one color. Diagonal values of `c`
are irrelevant. -/
def colorGraph (c : Sym2 V → Fin 7) (k : Fin 7) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c s(u,v) = k
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (c : Sym2 V → Fin 7) (k : Fin 7) : DecidableRel (colorGraph c k).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma balanced_compl_cliqueFree (c : Sym2 V → Fin 7) (hb : Balanced c) (k : Fin 7) :
    (colorGraph c k)ᶜ.CliqueFree 8 := by
  intro S hS
  apply hb S hS.card_eq k
  intro u hu v hv huv heq
  exact (hS.isClique hu hv huv).2 ⟨huv,heq⟩

lemma clique_card_lt_of_cliqueFree {G : SimpleGraph V} {n : Nat}
    (hf : G.CliqueFree n) {S : Finset V} (hs : G.IsClique S) : S.card < n := by
  by_contra h
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq (show n ≤ S.card by omega)
  exact hf T ⟨hs.subset hT,hcard⟩

/-- A proper k-coloring with independent sets of size at most a has
at most k*a vertices. -/
lemma card_le_of_colorable_and_independence {G : SimpleGraph V} {k a : Nat}
    (hc : G.Colorable k) (hi : Gᶜ.CliqueFree (a+1)) : Fintype.card V ≤ k*a := by
  classical
  obtain ⟨f⟩ := hc
  have hf : ∀ i : Fin k, (Finset.univ.filter (fun v => f v = i)).card ≤ a := by
    intro i
    have hcl : Gᶜ.IsClique (Finset.univ.filter (fun v => f v = i)) := by
      intro u hu v hv huv
      refine ⟨huv, fun hadj => f.valid hadj ?_⟩
      exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    have := clique_card_lt_of_cliqueFree hi hcl
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => hf i)
  have hpartition : (∑ i : Fin k, (Finset.univ.filter (fun v => f v = i)).card) =
      Fintype.card V := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simpa [hpartition] using hsum

lemma balanced_colorGraph_not_colorable (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : 50 ≤ Fintype.card V) (k : Fin 7) : ¬ (colorGraph c k).Colorable 7 := by
  intro hc
  have := card_le_of_colorable_and_independence hc (balanced_compl_cliqueFree c hb k)
  omega

/-- Brooks' theorem supplies a vertex of degree at least eight, unless
there is a monochromatic eight-clique. -/
lemma balanced_degree_obstruction (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : 50 ≤ Fintype.card V) (k : Fin 7)
    (hcf : (colorGraph c k).CliqueFree 8) : ∃ v, 8 ≤ (colorGraph c k).degree v := by
  by_contra h
  push Not at h
  have hdeg : ∀ v, (colorGraph c k).degree v ≤ 7 := by intro v; have := h v; omega
  exact balanced_colorGraph_not_colorable c hb hn k
    (Erdos617.R6.brooks_zajac 7 (by decide) (colorGraph c k) hdeg hcf)

end JSP500
