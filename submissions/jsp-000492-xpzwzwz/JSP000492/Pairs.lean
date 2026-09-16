import JSP000492.Geometry
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Set.Finite.Basic

namespace JSP000492

/-- Distance of an unordered pair, well-defined by symmetry of distance. -/
noncomputable def pairDistance : Sym2 E → ℝ :=
  Sym2.lift ⟨dist, fun _ _ => dist_comm _ _⟩

@[simp] theorem pairDistance_mk (x y : E) : pairDistance s(x, y) = dist x y := rfl

/-- Unordered pairs of distinct points at distance `sqrt 2`. -/
noncomputable def pairs (S : Finset E) : Finset (Sym2 E) := by
  classical
  exact S.sym2.filter fun e => ¬ e.IsDiag ∧ pairDistance e = Real.sqrt 2

/-- The number of unordered pairs of distinct points at distance `sqrt 2`. -/
noncomputable def pairCount (S : Finset E) : ℕ := (pairs S).card

@[simp] theorem mk_mem_pairs (S : Finset E) (x y : E) :
    s(x,y) ∈ pairs S ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ dist x y = Real.sqrt 2 := by
  classical
  simp [pairs, and_assoc]

theorem pairCount_mono {S T : Finset E} (h : S ⊆ T) : pairCount S ≤ pairCount T := by
  classical
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.sym2_mono h)

/-- An oriented collection with no reversed duplicate injects into unordered pairs. -/
theorem card_le_pairCount (S : Finset E) (D : Finset (E × E))
    (hmem : ∀ e ∈ D, e.1 ∈ S ∧ e.2 ∈ S ∧ dist e.1 e.2 = Real.sqrt 2)
    (hrev : ∀ u v, (u,v) ∈ D → (v,u) ∉ D) : D.card ≤ pairCount S := by
  classical
  let q : E × E → Sym2 E := fun p => s(p.1, p.2)
  have hinj : Set.InjOn q (D : Set (E × E)) := by
    intro e he f hf hef
    rcases Sym2.mk_eq_mk_iff.mp hef with h | h
    · exact h
    · exfalso
      apply hrev f.1 f.2 hf
      rw [h] at he
      exact he
  have hsub : D.image q ⊆ pairs S := by
    intro z hz
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hy,hd⟩ := hmem (x,y) hxy
    apply (mk_mem_pairs S x y).mpr
    refine ⟨hx,hy,?_,hd⟩
    intro h
    subst y
    exact hrev x x hxy hxy
  calc
    D.card = (D.image q).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ pairCount S := Finset.card_le_card hsub

/-- The unit sphere has infinitely many points, witnessed by normalized affine points. -/
theorem unitSphere_infinite : {v : E | ‖v‖ = 1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => point (n : ℝ) 0)
  · intro n m h
    have hp := point_injective (a₁ := ((n : ℝ), 0)) (a₂ := ((m : ℝ), 0)) h
    have hn : (n : ℝ) = (m : ℝ) := congrArg Prod.fst hp
    exact Nat.cast_injective hn
  · intro n
    exact point_norm _ _

end JSP000492
