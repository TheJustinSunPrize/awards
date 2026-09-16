import JSP500.FloorInfrastructure

namespace JSP500

open scoped Classical

/-- The first direct three-independence floor, obtained from the thirteen-vertex base. -/
theorem floor_three_twenty : EdgeFloor 3 20 63 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_two ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 6 := by omega
  have hf := floor_on_nonneighbors c hb k x floor_two_thirteen ha ho (by rw [hn,hd])
  have hs := star_small_bound c hb k x hm ho (by omega)
  rw [hd] at hs
  norm_num [starSmall] at hs
  omega

theorem floor_three_twenty_one : EdgeFloor 3 21 75 := by
  intro V _ _ c hb hn k ha ho
  by_contra he
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_two ha ho
  rw [hn] at havg hcore
  have hd : (colorGraph c k).degree x = 7 := by omega
  have hf := floor_on_nonneighbors c hb k x floor_two_thirteen ha ho (by rw [hn,hd])
  have hs := star_small_bound c hb k x hm ho (by omega)
  rw [hd] at hs
  norm_num [starSmall] at hs
  omega

/-- At order 38 the core ladder alone gives minimum degree eight. -/
theorem floor_five_thirty_eight : EdgeFloor 5 38 152 := by
  intro V _ _ c hb hn k ha ho
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_four ha ho
  rw [hn] at havg hcore
  omega

/-- At order 39 the core ladder alone gives minimum degree nine. -/
theorem floor_five_thirty_nine : EdgeFloor 5 39 176 := by
  intro V _ _ c hb hn k ha ho
  obtain ⟨x,hm⟩ := least_degree_vertex (colorGraph c k) (by omega)
  have havg := minimum_degree_average (colorGraph c k) x hm
  have hcore := nonneighbor_order_lt_core c hb k x core_four ha ho
  rw [hn] at havg hcore
  omega

end JSP500
