import JSP500.WeightedCoverBridge

namespace JSP500
open scoped Classical

lemma nonneighbor_finset_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (Gᶜ.neighborFinset x).card = Fintype.card V - 1 - G.degree x := by
  rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl]

theorem floor_four_twenty_eight : EdgeFloor 4 28 100 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_three ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 6 ∨ (colorGraph c k).degree x = 7 := by omega
  rcases hd with hd | hd
  · have hf := floor_on_nonneighbors c hb k x floor_three_twenty_one ha ho (by rw [hn,hd])
    exact six_neighbor_budget_impossible c hb k ha ho x hm hd (by omega)
      (by rw [nonneighbor_finset_card,hn,hd] <;> decide)
  · have hf := floor_on_nonneighbors c hb k x floor_three_twenty ha ho (by rw [hn,hd])
    exact seven_neighbor_budget_impossible c hb k ha ho x hm hd 6 (Or.inl rfl) (by omega)
      (by rw [nonneighbor_finset_card,hn,hd] <;> decide)

theorem floor_four_twenty_nine : EdgeFloor 4 29 113 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_three ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 7 := by omega
  have hf := floor_on_nonneighbors c hb k x floor_three_twenty_one ha ho (by rw [hn,hd])
  exact seven_neighbor_budget_impossible c hb k ha ho x hm hd 7 (Or.inr rfl) (by omega)
    (by rw [nonneighbor_finset_card,hn,hd] <;> decide)

theorem floor_five_thirty_five : EdgeFloor 5 35 122 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_four ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 5 ∨ (colorGraph c k).degree x = 6 := by omega
  have hs := star_small_bound c hb k x hm ho (by omega)
  rcases hd with hd | hd
  · have hf := floor_on_nonneighbors c hb k x floor_four_twenty_nine ha ho (by rw [hn,hd])
    rw [hd] at hs
    norm_num [starSmall,Nat.choose_two_right] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_four_twenty_eight ha ho (by rw [hn,hd])
    rw [hd] at hs
    norm_num [starSmall] at hs
    omega

theorem floor_five_thirty_six : EdgeFloor 5 36 134 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_four ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 6 ∨ (colorGraph c k).degree x = 7 := by omega
  have hs := star_small_bound c hb k x hm ho (by omega)
  rcases hd with hd | hd
  · have hf := floor_on_nonneighbors c hb k x floor_four_twenty_nine ha ho (by rw [hn,hd])
    rw [hd] at hs
    norm_num [starSmall] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_four_twenty_eight ha ho (by rw [hn,hd])
    rw [hd] at hs
    norm_num [starSmall] at hs
    omega

theorem floor_five_thirty_seven : EdgeFloor 5 37 147 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_four ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 7 := by omega
  have hs := star_small_bound c hb k x hm ho (by omega)
  have hf := floor_on_nonneighbors c hb k x floor_four_twenty_nine ha ho (by rw [hn,hd])
  rw [hd] at hs
  norm_num [starSmall] at hs
  omega

theorem floor_six_forty_three : EdgeFloor 6 43 156 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_five ha ho
  rw [hn] at havg hcore
  have hdlo : 3 ≤ (colorGraph c k).degree x := by omega
  have hdhi : (colorGraph c k).degree x ≤ 7 := by omega
  have hs := star_small_bound c hb k x hm ho hdhi
  interval_cases hd : (colorGraph c k).degree x
  · have hf := floor_on_nonneighbors c hb k x floor_five_thirty_nine ha ho (by rw [hn,hd])
    norm_num [starSmall,Nat.choose_two_right] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_five_thirty_eight ha ho (by rw [hn,hd])
    norm_num [starSmall,Nat.choose_two_right] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_five_thirty_seven ha ho (by rw [hn,hd])
    norm_num [starSmall,Nat.choose_two_right] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_five_thirty_six ha ho (by rw [hn,hd])
    norm_num [starSmall] at hs
    omega
  · have hf := floor_on_nonneighbors c hb k x floor_five_thirty_five ha ho (by rw [hn,hd])
    norm_num [starSmall] at hs
    omega

end JSP500
