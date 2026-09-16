import SendovDirectionGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.EquivFin

/-! A necessary direction model for arbitrary finite planar configurations.
The missing general cardinality inequality for this model is not assumed or proved.
-/
namespace SendovDirectionModel
open Real SendovDirectionGeometry

structure Model (N : ℕ) (t : ℝ) where
  theta : Fin N → Fin N → ℝ
  range : ∀ i j, i < j → 0 ≤ theta i j ∧ theta i j < t
  triangle : ∀ i j k, i < j → j < k →
    SendovFiveDirections.Triangle t (theta i j) (theta i k) (theta j k)

/-- Every angularly capped configuration yields the direction constraints,
for arbitrary cardinality. The labels are obtained by a generic similarity
and reindexing; the statement has no general-position assumption. -/
theorem model_of_complex_points {N : ℕ} {p : Fin N → ℂ} {lam : ℝ}
    (hp : Function.Injective p) (hlam : 0 < lam)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ π-lam) :
    Nonempty (Model N (π/lam)) := by
  obtain ⟨z,hz,hre⟩ := exists_generic_multiplier p hp
  obtain ⟨index,hi,hsort⟩ := exists_sorted_indices (fun i => (z*p i).re) hre
  let q : Fin N → ℂ := fun i => z*p (index i)
  have hq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (q i) (q j) (q k) ≤ π-lam := by
    intro i j k hij hik hjk
    change InnerProductGeometry.angle (z*p (index i)-z*p (index j))
      (z*p (index k)-z*p (index j)) ≤ π-lam
    rw [← mul_sub, ← mul_sub, Complex.angle_mul_left hz]
    exact hangle (index i) (index j) (index k)
      (fun h => hij (hi h)) (fun h => hik (hi h)) (fun h => hjk (hi h))
  refine ⟨⟨(fun i j => normalize lam (q j-q i).arg), ?_, ?_⟩⟩
  · intro i j hij
    exact normalized_arg_range hlam (by simpa [q] using sub_pos.mpr (hsort hij))
  · intro i j k hij hjk
    exact triangle_labels hlam (hsort hij) (hsort hjk)
      (hq j i k (ne_of_gt hij) (ne_of_lt hjk) (ne_of_lt (hij.trans hjk)))
      (hq i j k (ne_of_lt hij) (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk))
      (hq i k j (ne_of_lt (hij.trans hjk)) (ne_of_lt hij) (ne_of_gt hjk))

abbrev Point := EuclideanSpace ℝ (Fin 2)

theorem model_of_plane_points {N : ℕ} {p : Fin N → Point} {lam : ℝ}
    (hp : Function.Injective p) (hlam : 0 < lam)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ π-lam) :
    Nonempty (Model N (π/lam)) := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  apply model_of_complex_points (e.injective.comp hp) hlam
  intro i j k hij hik hjk
  change InnerProductGeometry.angle (e (p i)-e (p j))
    (e (p k)-e (p j)) ≤ π-lam
  rw [← map_sub, ← map_sub]
  change InnerProductGeometry.angle (e.toLinearIsometry (p i-p j))
    (e.toLinearIsometry (p k-p j)) ≤ π-lam
  rw [e.toLinearIsometry.angle_map]
  exact hangle i j k hij hik hjk

/-- Finite-set version: its cardinality is exactly the direction-model size. -/
theorem model_of_finite_set (s : Finset Point) {lam : ℝ} (hlam : 0 < lam)
    (hangle : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle a b c ≤ π-lam) :
    Nonempty (Model s.card (π/lam)) := by
  classical
  let e := s.equivFin.symm
  let p : Fin s.card → Point := fun i => (e i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  apply model_of_plane_points hp hlam
  intro i j k hij hik hjk
  exact hangle (p i) (e i).property (p j) (e j).property (p k) (e k).property
    (fun h => hij (hp h)) (fun h => hik (hp h)) (fun h => hjk (hp h))

/-- A proved bound on all direction models would transfer to actual point sets.
The model bound is an explicit hypothesis, not an established general result. -/
theorem card_bound_transfer (B : ℝ → ℕ)
    (bound : ∀ N t, Nonempty (Model N t) → N ≤ B t)
    (s : Finset Point) {lam : ℝ} (hlam : 0 < lam)
    (hangle : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle a b c ≤ π-lam) :
    s.card ≤ B (π/lam) :=
  bound _ _ (model_of_finite_set s hlam hangle)

#print axioms model_of_complex_points
#print axioms model_of_plane_points
#print axioms model_of_finite_set
#print axioms card_bound_transfer
end SendovDirectionModel

