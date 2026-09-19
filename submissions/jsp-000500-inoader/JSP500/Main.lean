import JSP500.UnrestrictedFloors

open Finset
open scoped BigOperators Classical

namespace JSP500
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The ordinary star bound does not require excluding seven-cliques. -/
lemma star_basic_bound (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hm : ∀ v, G.degree x ≤ G.degree v) (hd : G.degree x ≤ 6) :
    edgeCount G (Gᶜ.neighborFinset x) + (G.degree x+1).choose 2 ≤ G.edgeFinset.card := by
  have h := minimum_degree_accounting G x hm
  have ht := edgeCount_le_choose_two G (G.neighborFinset x)
  rw [G.card_neighborFinset_eq_degree] at ht
  interval_cases G.degree x <;>
    norm_num only [Nat.choose_two_right] at h ht ⊢ <;> omega

lemma color_floor_on_nonneighbors (c : Sym2 V → Fin 7) (hb : Balanced c)
    (k : Fin 7) (x : V) {a n b : Nat} (hf : ColorFloor a n b)
    (ha : (colorGraph c k)ᶜ.CliqueFree (a+2))
    (hn : Fintype.card V - 1 - (colorGraph c k).degree x = n) :
    b ≤ edgeCount (colorGraph c k) ((colorGraph c k)ᶜ.neighborFinset x) := by
  have h := hf _ (restrictColor c _) (balanced_restrict c hb _)
    (by rw [nonneighbor_card]; exact hn) k (nonneighbor_alpha_drop c k x ha)
  rwa [edgeCount_restrict_color] at h

/-- There is no balanced seven-coloring on fifty vertices. -/
theorem no_balanced_fifty (c : Sym2 V → Fin 7) (hn : Fintype.card V = 50) : ¬ Balanced c := by
  intro hb
  obtain ⟨k,he⟩ := exists_color_budget c hn
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  obtain ⟨w,hw⟩ := degree_at_most_six c hb hn k he
  have hd : (colorGraph c k).degree x ≤ 6 := (hm w).trans hw
  have ha := balanced_compl_cliqueFree c hb k
  have hs := star_basic_bound (colorGraph c k) x hm hd
  interval_cases hx : (colorGraph c k).degree x
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_nine ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_eight ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_seven ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_six ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_five ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_four ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega
  · have hf := color_floor_on_nonneighbors c hb k x color_floor_six_forty_three ha (by rw [hn,hx])
    norm_num only [Nat.choose_two_right] at hs
    omega

/-- Exact fixed-r=7 statement: every seven-coloring of K50 has an eight-set
whose induced edges omit a color. -/
theorem main_proven : Main := by
  rw [main_iff_no_balanced]
  intro c
  exact no_balanced_fifty c (by simp)

/-- The same theorem on any finite vertex type of cardinality fifty. -/
theorem upstream_proven : Upstream := by
  intro V _ _ hn c
  have h := no_balanced_fifty c hn
  simpa only [Balanced,not_forall,not_not,exists_prop] using h

end JSP500
