import SendovDirectionGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.EquivFin

/-! A finite-set statement of the five-point lower bound in the standard
Euclidean plane. This is a special case, not the general Sendov classification. -/
namespace SendovFivePointPlane
open Real
abbrev Point := EuclideanSpace ℝ (Fin 2)

theorem five_points_large_angle {p : Fin 5 → Point} (hp : Function.Injective p) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      3*π/5 ≤ EuclideanGeometry.angle (p i) (p j) (p k) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨i,j,k,hij,hik,hjk,hangle⟩ :=
    SendovDirectionGeometry.five_points_large_angle (e.injective.comp hp)
  refine ⟨i,j,k,hij,hik,hjk,?_⟩
  change 3*π/5 ≤ InnerProductGeometry.angle (e (p i)-e (p j))
    (e (p k)-e (p j)) at hangle
  rw [← map_sub, ← map_sub] at hangle
  change 3*π/5 ≤ InnerProductGeometry.angle
    (e.toLinearIsometry (p i-p j)) (e.toLinearIsometry (p k-p j)) at hangle
  rw [e.toLinearIsometry.angle_map] at hangle
  exact hangle

/-- Any finite set of at least five distinct Euclidean points contains a
pairwise-distinct triple forming an angle of at least `3*pi/5`. -/
theorem finite_set_large_angle (s : Finset Point) (hs : 5 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 3*π/5 ≤ EuclideanGeometry.angle a b c := by
  classical
  obtain ⟨t,ht,hcard⟩ := Finset.exists_subset_card_eq hs
  let e := (Finset.equivFinOfCardEq hcard).symm
  let p : Fin 5 → Point := fun i => (e i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  obtain ⟨i,j,k,hij,hik,hjk,hangle⟩ := five_points_large_angle hp
  exact ⟨p i, ht (e i).property, p j, ht (e j).property,
    p k, ht (e k).property,
    (fun h => hij (hp h)), (fun h => hik (hp h)), (fun h => hjk (hp h)), hangle⟩

#print axioms five_points_large_angle
#print axioms finite_set_large_angle
end SendovFivePointPlane
