import JSP500.ExtremalBounds

open Finset
open scoped BigOperators

namespace JSP500

/-- No balanced coloring has a color graph of this order with independence
number at most `a` and clique number at most six. -/
def CoreExcluded (a n : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (c : Sym2 V → Fin 7), Balanced c →
    n ≤ Fintype.card V → ∀ k,
    (colorGraph c k)ᶜ.CliqueFree (a+1) → (colorGraph c k).CliqueFree 7 → False

lemma coreExcluded_of_exact (a n : Nat)
    (hexact : ∀ (V : Type) [Fintype V] [DecidableEq V] (c : Sym2 V → Fin 7), Balanced c →
      Fintype.card V = n → ∀ k,
      (colorGraph c k)ᶜ.CliqueFree (a+1) → (colorGraph c k).CliqueFree 7 → False) :
    CoreExcluded a n := by
  intro V _ _ c hb hn k ha ho
  classical
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset V).card by simpa using hn)
  apply hexact ↥S (restrictColor c S) (balanced_restrict c hb S) (by simpa using hS) k
  · rw [compl_colorGraph_restrict]
    exact Erdos617.R6.Brooks.cliqueFree_comap (colorGraph c k)ᶜ S ha
  · rw [colorGraph_restrict]
    exact Erdos617.R6.Brooks.cliqueFree_comap (colorGraph c k) S ho

lemma cliqueFree_neighbor_comap {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a : Nat} (ha : G.CliqueFree (a+1)) (v : V) :
    (G.comap (Subtype.val : ↥(G.neighborFinset v) → V)).CliqueFree a := by
  classical
  intro T hT
  have hcl : G.IsNClique a (T.image Subtype.val) := by
    constructor
    · intro x hx y hy hxy
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
      exact hT.isClique hx' hy' (fun h => hxy (congrArg Subtype.val h))
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, hT.card_eq]
  apply ha _ (hcl.insert (a := v) ?_)
  intro x hx
  obtain ⟨x',_,rfl⟩ := Finset.mem_image.mp hx
  exact (G.mem_neighborFinset v x').mp x'.property

lemma core_ladder_step (a previous n b : Nat) (ih : CoreExcluded a previous)
    (hlarge : 15 ≤ n) (horder : 7*(a+1) < n)
    (hlower : SimpleGraph.turanNumber n 7 + b ≤ n.choose 2 + (n/7-1))
    (hgap : n*(previous-1) < 12*b) : CoreExcluded (a+1) n := by
  apply coreExcluded_of_exact
  intro V _ _ c hb hn k ha ho
  classical
  let L := (colorGraph c k)ᶜ
  have hdeg : ∀ v, L.degree v ≤ previous-1 := by
    intro v
    have hlt : L.degree v < previous := by
      by_contra h
      let S := L.neighborFinset v
      apply ih ↥S (restrictColor c S) (balanced_restrict c hb S)
        (by simpa only [Fintype.card_coe, S, L.card_neighborFinset_eq_degree] using (show previous ≤ L.degree v by omega)) k
      · rw [compl_colorGraph_restrict]
        exact cliqueFree_neighbor_comap L ha v
      · rw [colorGraph_restrict]
        exact Erdos617.R6.Brooks.cliqueFree_comap (colorGraph c k) S ho
    omega
  have hupper : 2*L.edgeFinset.card ≤ n*(previous-1) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdeg v)
    simpa [L.sum_degrees_eq_twice_card_edges, hn] using h
  have hother : ∀ j : Fin 7, j ≠ k → b ≤ (colorGraph c j).edgeFinset.card := by
    intro j hj
    have h := strict_other_color_bound c hb hj.symm ha (by omega) (by omega)
    rw [hn] at h
    omega
  have hrest : 6*b ≤ ∑ j ∈ Finset.univ.erase k, (colorGraph c j).edgeFinset.card := by
    calc
      _ = ∑ _j ∈ (Finset.univ : Finset (Fin 7)).erase k, b := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hother j (Finset.ne_of_mem_erase hj))
  have hsum := sum_edgesOn c Finset.univ
  simp only [edgesOn_univ, Finset.card_univ] at hsum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)] at hsum
  have hp := edges_add_complement (colorGraph c k)
  change (colorGraph c k).edgeFinset.card + L.edgeFinset.card = _ at hp
  omega

theorem core_two : CoreExcluded 2 14 := by
  intro V _ _ c hb hn k ha ho
  exact no_colored_terminal c hb hn k ha ho

theorem core_three : CoreExcluded 3 22 := by
  apply core_ladder_step 2 14 22 26 core_two (by decide) (by decide)
  · norm_num [SimpleGraph.turanNumber_eq, Nat.choose_two_right]
  · decide

theorem core_four : CoreExcluded 4 30 := by
  apply core_ladder_step 3 22 30 53 core_three (by decide) (by decide)
  · norm_num [SimpleGraph.turanNumber_eq, Nat.choose_two_right]
  · decide

theorem core_five : CoreExcluded 5 40 := by
  apply core_ladder_step 4 30 40 99 core_four (by decide) (by decide)
  · norm_num [SimpleGraph.turanNumber_eq, Nat.choose_two_right]
  · decide

end JSP500
