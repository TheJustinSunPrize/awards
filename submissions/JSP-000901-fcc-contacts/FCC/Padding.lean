import FCC.Geometry

namespace FCC

open Finset

theorem coord_bounds {m : ℕ} (v : Vertex m) (i : Fin 3) :
    0 ≤ coord v i ∧ coord v i < 2 * m := by
  rcases v with ⟨a, x, y, z⟩
  fin_cases a <;> fin_cases i <;>
    simp [coord, cellCoord, offset, Fin.ext_iff] <;> omega

theorem point_first_le {m : ℕ} (v : Vertex m) : (point v) 0 ≤ 2 * m := by
  change (coord v 0 : ℝ) / Real.sqrt 2 ≤ 2 * m
  have hc : (coord v 0 : ℝ) ≤ 2 * m := by exact_mod_cast (coord_bounds v 0).2.le
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem two_le_dist_of_first_gap (x y : EuclideanSpace ℝ (Fin 3))
    (h : x 0 + 2 ≤ y 0) : 2 ≤ dist x y := by
  have hsq : (x 0 - y 0) ^ 2 ≤ dist x y ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simpa only [Real.dist_eq, sq_abs] using
      (single_le_sum (f := fun i : Fin 3 => dist (x i) (y i) ^ 2)
        (fun i _ => sq_nonneg (dist (x i) (y i))) (mem_univ 0))
  nlinarith [dist_nonneg (x := x) (y := y), sq_nonneg (y 0 - x 0 - 2)]

noncomputable def farPoint (m i : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![((2 * m + 2 + 2 * i : ℕ) : ℝ), 0, 0]

noncomputable def paddedPoint {m q : ℕ} : Vertex m ⊕ Fin q → EuclideanSpace ℝ (Fin 3)
  | .inl v => point v
  | .inr i => farPoint m i

theorem point_far_dist {m : ℕ} (v : Vertex m) (i : ℕ) :
    2 ≤ dist (point v) (farPoint m i) := by
  apply two_le_dist_of_first_gap
  have hv := point_first_le v
  change (point v) 0 + 2 ≤ ((2 * m + 2 + 2 * i : ℕ) : ℝ)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

theorem farPoint_dist {m i j : ℕ} (hij : i ≠ j) :
    2 ≤ dist (farPoint m i) (farPoint m j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · apply two_le_dist_of_first_gap
    change ((2 * m + 2 + 2 * i : ℕ) : ℝ) + 2 ≤ ((2 * m + 2 + 2 * j : ℕ) : ℝ)
    exact_mod_cast (show 2 * m + 2 + 2 * i + 2 ≤ 2 * m + 2 + 2 * j by omega)
  · rw [dist_comm]
    apply two_le_dist_of_first_gap
    change ((2 * m + 2 + 2 * j : ℕ) : ℝ) + 2 ≤ ((2 * m + 2 + 2 * i : ℕ) : ℝ)
    exact_mod_cast (show 2 * m + 2 + 2 * j + 2 ≤ 2 * m + 2 + 2 * i by omega)

theorem paddedPoint_separated {m q : ℕ} {u v : Vertex m ⊕ Fin q} (huv : u ≠ v) :
    1 ≤ dist (paddedPoint u) (paddedPoint v) := by
  rcases u with u | u <;> rcases v with v | v
  · exact point_separated (fun h => huv (congrArg Sum.inl h))
  · exact le_trans (by norm_num) (point_far_dist u v)
  · rw [dist_comm]
    exact le_trans (by norm_num) (point_far_dist v u)
  · have h : (u : ℕ) ≠ (v : ℕ) := by
      intro he
      exact huv (congrArg Sum.inr (Fin.ext he))
    exact le_trans (by norm_num) (farPoint_dist h)

theorem paddedPoint_injective {m q : ℕ} : Function.Injective (@paddedPoint m q) := by
  intro u v h
  by_contra huv
  have hd := paddedPoint_separated huv
  rw [h, dist_self] at hd
  norm_num at hd

/-- The added points introduce no new contacts. -/
theorem paddedPoint_contact_iff {m q : ℕ} (u v : Vertex m ⊕ Fin q) :
    dist (paddedPoint u) (paddedPoint v) = 1 ↔
      ∃ a b : Vertex m, u = Sum.inl a ∧ v = Sum.inl b ∧ Contact a b := by
  rcases u with u | u <;> rcases v with v | v
  · constructor
    · intro h
      exact ⟨u, v, rfl, rfl, (point_dist_eq_one_iff u v).mp h⟩
    · rintro ⟨a, b, ha, hb, hc⟩
      have ha' : u = a := Sum.inl.inj ha
      have hb' : v = b := Sum.inl.inj hb
      subst a
      subst b
      exact (point_dist_eq_one_iff u v).mpr hc
  · constructor
    · intro h
      have hd := point_far_dist u v
      change dist (point u) (farPoint m v) = 1 at h
      linarith
    · rintro ⟨a, b, _, hb, _⟩
      cases hb
  · constructor
    · intro h
      have hd := point_far_dist v u
      change dist (farPoint m u) (point v) = 1 at h
      rw [dist_comm] at h
      linarith
    · rintro ⟨a, b, ha, _, _⟩
      cases ha
  · constructor
    · intro hdist
      by_cases h : u = v
      · subst v
        simp at hdist
      · have hd := farPoint_dist (m := m) (i := u) (j := v) (fun he => h (Fin.ext he))
        change dist (farPoint m u) (farPoint m v) = 1 at hdist
        linarith
    · rintro ⟨a, b, ha, _, _⟩
      cases ha

noncomputable def paddedPoints (m q : ℕ) : Finset (EuclideanSpace ℝ (Fin 3)) := by
  classical
  exact univ.image (@paddedPoint m q)

theorem paddedPoints_card (m q : ℕ) : (paddedPoints m q).card = 4 * m ^ 3 + q := by
  classical
  rw [paddedPoints, card_image_of_injective _ paddedPoint_injective, card_univ,
    Fintype.card_sum, vertex_card, Fintype.card_fin]

theorem paddedPoints_separated (m q : ℕ) :
    (paddedPoints m q : Set (EuclideanSpace ℝ (Fin 3))).Pairwise
      (fun x y => 1 ≤ dist x y) := by
  classical
  intro x hx y hy hxy
  obtain ⟨u, _, rfl⟩ := mem_image.mp hx
  obtain ⟨v, _, rfl⟩ := mem_image.mp hy
  exact paddedPoint_separated (fun h => hxy (congrArg paddedPoint h))

end FCC
