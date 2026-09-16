import Statement

namespace JSP000194

private lemma collinear_swap_last (a b c : Point) :
    Collinear a b c ↔ Collinear a c b := by
  unfold Collinear
  constructor <;> intro h <;> nlinarith

private lemma collinear_cycle (a b c : Point) :
    Collinear a b c ↔ Collinear b c a := by
  unfold Collinear
  constructor <;> intro h <;> nlinarith

private lemma collinear_first_repeat (a b : Point) : Collinear a b a := by
  unfold Collinear
  ring

private lemma collinear_last_repeat (a b : Point) : Collinear a b b := by
  unfold Collinear
  ring

/-- For three distinct non-collinear points, each of the three connecting
lines contains exactly its two defining points. -/
theorem three_point_ordinary_lines
    (a b c : Point)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnoncol : ¬ Collinear a b c) :
    ThreePointOrdinary a b c := by
  have h_acb : ¬ Collinear a c b := by
    intro h
    exact hnoncol ((collinear_swap_last a b c).mpr h)
  have h_bca : ¬ Collinear b c a := by
    intro h
    exact hnoncol ((collinear_cycle a b c).mpr h)
  have hab_ord : OrdinaryLine ({a, b, c} : Set Point) a b := by
    refine ⟨by simp, by simp, hab, ?_⟩
    intro x hx hcol
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hnoncol hcol)
  have hac_ord : OrdinaryLine ({a, b, c} : Set Point) a c := by
    refine ⟨by simp, by simp, hac, ?_⟩
    intro x hx hcol
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (h_acb hcol)
    · exact Or.inr rfl
  have hbc_ord : OrdinaryLine ({a, b, c} : Set Point) b c := by
    refine ⟨by simp, by simp, hbc, ?_⟩
    intro x hx hcol
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact False.elim (h_bca hcol)
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hab_ne_hac : LineThrough a b ≠ LineThrough a c := by
    intro hlines
    have hc_ac : c ∈ LineThrough a c := by
      change Collinear a c c
      exact collinear_last_repeat a c
    have hc_ab : c ∈ LineThrough a b := by
      rw [hlines]
      exact hc_ac
    change Collinear a b c at hc_ab
    exact hnoncol hc_ab
  have hab_ne_hbc : LineThrough a b ≠ LineThrough b c := by
    intro hlines
    have hc_bc : c ∈ LineThrough b c := by
      change Collinear b c c
      exact collinear_last_repeat b c
    have hc_ab : c ∈ LineThrough a b := by
      rw [hlines]
      exact hc_bc
    change Collinear a b c at hc_ab
    exact hnoncol hc_ab
  have hac_ne_hbc : LineThrough a c ≠ LineThrough b c := by
    intro hlines
    have hb_bc : b ∈ LineThrough b c := by
      change Collinear b c b
      exact collinear_first_repeat b c
    have hb_ac : b ∈ LineThrough a c := by
      rw [hlines]
      exact hb_bc
    change Collinear a c b at hb_ac
    exact h_acb hb_ac
  exact ⟨hab_ord, hac_ord, hbc_ord, hab_ne_hac, hab_ne_hbc, hac_ne_hbc⟩

end JSP000194
