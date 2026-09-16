import SendovDirectionModel
import SendovSixDirections

/-! A six-point lower bound transferred from the necessary direction model.
This is a finite special case, not the general Sendov classification. -/
namespace SendovSixPointPlane
open Real SendovDirectionModel

theorem model_bound {t : ℝ} (m : Model 6 t) : 3 ≤ t := by
  exact SendovSixDirections.three_le t
    (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
    (m.range 0 1 (by decide))
    (m.range 0 2 (by decide))
    (m.range 0 3 (by decide))
    (m.range 0 4 (by decide))
    (m.range 0 5 (by decide))
    (m.range 1 2 (by decide))
    (m.range 1 3 (by decide))
    (m.range 1 4 (by decide))
    (m.range 1 5 (by decide))
    (m.range 2 3 (by decide))
    (m.range 2 4 (by decide))
    (m.range 2 5 (by decide))
    (m.range 3 4 (by decide))
    (m.range 3 5 (by decide))
    (m.range 4 5 (by decide))
    (m.triangle 0 1 2 (by decide) (by decide))
    (m.triangle 0 1 3 (by decide) (by decide))
    (m.triangle 0 1 4 (by decide) (by decide))
    (m.triangle 0 1 5 (by decide) (by decide))
    (m.triangle 0 2 3 (by decide) (by decide))
    (m.triangle 0 2 4 (by decide) (by decide))
    (m.triangle 0 2 5 (by decide) (by decide))
    (m.triangle 0 3 4 (by decide) (by decide))
    (m.triangle 0 3 5 (by decide) (by decide))
    (m.triangle 0 4 5 (by decide) (by decide))
    (m.triangle 1 2 3 (by decide) (by decide))
    (m.triangle 1 2 4 (by decide) (by decide))
    (m.triangle 1 2 5 (by decide) (by decide))
    (m.triangle 1 3 4 (by decide) (by decide))
    (m.triangle 1 3 5 (by decide) (by decide))
    (m.triangle 1 4 5 (by decide) (by decide))
    (m.triangle 2 3 4 (by decide) (by decide))
    (m.triangle 2 3 5 (by decide) (by decide))
    (m.triangle 2 4 5 (by decide) (by decide))
    (m.triangle 3 4 5 (by decide) (by decide))

theorem six_point_cap {p : Fin 6 → Point} {lam : ℝ}
    (hp : Function.Injective p) (hlam : 0 < lam)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ π-lam) :
    lam ≤ π/3 := by
  obtain ⟨m⟩ := model_of_plane_points hp hlam hangle
  have hb := (le_div_iff₀ hlam).mp (model_bound m)
  linarith

theorem six_points_large_angle {p : Fin 6 → Point} (hp : Function.Injective p) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      2*π/3 ≤ EuclideanGeometry.angle (p i) (p j) (p k) := by
  classical
  let triples : Finset (Fin 6 × Fin 6 × Fin 6) :=
    Finset.univ.filter (fun v => v.1 ≠ v.2.1 ∧ v.1 ≠ v.2.2 ∧ v.2.1 ≠ v.2.2)
  have hn : triples.Nonempty := by
    refine ⟨(0,1,2), ?_⟩
    simp [triples]
  obtain ⟨v,hv,hmax⟩ := triples.exists_max_image
    (fun v => EuclideanGeometry.angle (p v.1) (p v.2.1) (p v.2.2)) hn
  have hd := (Finset.mem_filter.mp hv).2
  refine ⟨v.1,v.2.1,v.2.2,hd.1,hd.2.1,hd.2.2,?_⟩
  by_contra h
  have hsmall := lt_of_not_ge h
  let M := EuclideanGeometry.angle (p v.1) (p v.2.1) (p v.2.2)
  have hlam : 0 < π-M := by dsimp [M]; linarith [Real.pi_pos]
  have hcap : π-M ≤ π/3 := six_point_cap hp hlam (by
    intro i j k hij hik hjk
    have hm := hmax (i,j,k) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hij,hik,hjk⟩)
    dsimp at hm
    dsimp [M]
    linarith)
  dsimp [M] at hcap
  linarith

theorem finite_set_large_angle (s : Finset Point) (hs : 6 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 2*π/3 ≤ EuclideanGeometry.angle a b c := by
  classical
  obtain ⟨t,ht,hcard⟩ := Finset.exists_subset_card_eq hs
  let e := (Finset.equivFinOfCardEq hcard).symm
  let p : Fin 6 → Point := fun i => (e i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  obtain ⟨i,j,k,hij,hik,hjk,hangle⟩ := six_points_large_angle hp
  exact ⟨p i, ht (e i).property, p j, ht (e j).property,
    p k, ht (e k).property,
    (fun h => hij (hp h)), (fun h => hik (hp h)), (fun h => hjk (hp h)), hangle⟩

#print axioms model_bound
#print axioms six_point_cap
#print axioms six_points_large_angle
#print axioms finite_set_large_angle
end SendovSixPointPlane

