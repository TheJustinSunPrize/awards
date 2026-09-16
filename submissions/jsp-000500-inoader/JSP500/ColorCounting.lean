import JSP500.ColoringBounds

open Finset
open scoped BigOperators

namespace JSP500

variable {V : Type} [Fintype V] [DecidableEq V]

def pairsOn (S : Finset V) : Finset (Sym2 V) := S.offDiag.image Sym2.mk.uncurry

def edgesOn (c : Sym2 V → Fin 7) (S : Finset V) (k : Fin 7) : Finset (Sym2 V) :=
  (pairsOn S).filter (fun e => c e = k)

lemma mk_mem_pairsOn {S : Finset V} {u v : V} :
    s(u,v) ∈ pairsOn S ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  simp only [pairsOn, Finset.mem_image, Finset.mem_offDiag, Prod.exists,
    Function.uncurry_apply_pair, Sym2.eq_iff]
  constructor
  · rintro ⟨a,b,⟨ha,hb,hab⟩,he⟩
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨ha,hb,hab⟩
    · exact ⟨hb,ha,hab.symm⟩
  · rintro ⟨hu,hv,huv⟩
    exact ⟨u,v,⟨hu,hv,huv⟩,Or.inl ⟨rfl,rfl⟩⟩

lemma edgesOn_univ (c : Sym2 V → Fin 7) (k : Fin 7) :
    edgesOn c Finset.univ k = (colorGraph c k).edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset]
    simp [edgesOn, mk_mem_pairsOn, colorGraph]

lemma sum_edgesOn (c : Sym2 V → Fin 7) (S : Finset V) :
    (∑ k, (edgesOn c S k).card) = S.card.choose 2 := by
  calc
    _ = (pairsOn S).card := (Finset.card_eq_sum_card_fiberwise
      (s := pairsOn S) (f := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm
    _ = _ := Sym2.card_image_offDiag S

lemma balanced_edgesOn_positive (c : Sym2 V → Fin 7) (hb : Balanced c)
    (S : Finset V) (hS : S.card = 8) (k : Fin 7) : 1 ≤ (edgesOn c S k).card := by
  have h := hb S hS k
  simp only [Misses, not_forall, not_not, exists_prop] at h
  obtain ⟨u,hu,v,hv,huv,hc⟩ := h
  apply Finset.one_le_card.mpr
  exact ⟨s(u,v), Finset.mem_filter.mpr ⟨mk_mem_pairsOn.mpr ⟨hu,hv,huv⟩,hc⟩⟩

/-- Every induced eight-set has at most 22 edges of one color. -/
theorem local_cap_twenty_two (c : Sym2 V → Fin 7) (hb : Balanced c)
    (S : Finset V) (hS : S.card = 8) (k : Fin 7) : (edgesOn c S k).card ≤ 22 := by
  have hsum := sum_edgesOn c S
  rw [hS] at hsum
  norm_num [Nat.choose_two_right] at hsum
  have hk : k ∈ (Finset.univ : Finset (Fin 7)) := Finset.mem_univ k
  rw [← Finset.sum_erase_add _ _ hk] at hsum
  have hrest : 6 ≤ ∑ j ∈ Finset.univ.erase k, (edgesOn c S j).card := by
    calc
      6 = ∑ _j ∈ (Finset.univ : Finset (Fin 7)).erase k, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => balanced_edgesOn_positive c hb S hS j)
  omega

lemma balanced_colorGraph_cliqueFree (c : Sym2 V → Fin 7) (hb : Balanced c)
    (k : Fin 7) : (colorGraph c k).CliqueFree 8 := by
  intro S hS
  have hc := local_cap_twenty_two c hb S hS.card_eq k
  have heq : edgesOn c S k = pairsOn S := by
    apply Finset.filter_eq_self.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨hu,hv,huv⟩ := mk_mem_pairsOn.mp he
      exact (hS.isClique hu hv huv).2
  rw [heq] at hc
  have hcard : (pairsOn S).card = 28 := by
    rw [pairsOn, Sym2.card_image_offDiag, hS.card_eq]
    decide
  omega

/-- A least color on 50 vertices has at most 175 edges. -/
theorem exists_color_budget (c : Sym2 V → Fin 7) (hn : Fintype.card V = 50) :
    ∃ k, (colorGraph c k).edgeFinset.card ≤ 175 := by
  have hsum := sum_edgesOn c Finset.univ
  simp only [edgesOn_univ, Finset.card_univ, hn] at hsum
  norm_num [Nat.choose_two_right] at hsum
  by_contra h
  push Not at h
  have hlow : (∑ _k : Fin 7, 176) ≤ ∑ k, (colorGraph c k).edgeFinset.card :=
    Finset.sum_le_sum (fun k _ => by have := h k; omega)
  norm_num at hlow
  omega

/-- A color with at most 175 edges must have a vertex of degree at most six. -/
theorem degree_at_most_six (c : Sym2 V → Fin 7) (hb : Balanced c)
    (hn : Fintype.card V = 50) (k : Fin 7)
    (he : (colorGraph c k).edgeFinset.card ≤ 175) :
    ∃ v, (colorGraph c k).degree v ≤ 6 := by
  by_contra h
  push Not at h
  have hge : ∀ v, 7 ≤ (colorGraph c k).degree v := by intro v; have := h v; omega
  have hsum := (colorGraph c k).sum_degrees_eq_twice_card_edges
  have hlow : (∑ _v : V, 7) ≤ ∑ v, (colorGraph c k).degree v :=
    Finset.sum_le_sum (fun v _ => hge v)
  have htotal : (∑ _v : V, 7) = ∑ v, (colorGraph c k).degree v := by
    simp only [Finset.sum_const, Finset.card_univ, hn, smul_eq_mul] at hlow ⊢
    omega
  have hreg : ∀ v, (colorGraph c k).degree v = 7 := by
    have hh := (Finset.sum_eq_sum_iff_of_le
      (fun v (_ : v ∈ (Finset.univ : Finset V)) => hge v)).mp htotal
    exact fun v => (hh v (Finset.mem_univ v)).symm
  obtain ⟨v,hv⟩ := balanced_degree_obstruction c hb (by omega) k
    (balanced_colorGraph_cliqueFree c hb k)
  have := hreg v
  omega

end JSP500
