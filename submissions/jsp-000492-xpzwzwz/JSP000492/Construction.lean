import JSP000492.Geometry
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace JSP000492

open Finset

/-- The finite incidence construction, isolated from the Euclidean realization. -/
theorem grid_construction {V : Type*} [NormedAddCommGroup V]
    (p l : ℕ → ℕ → V)
    (hp : Function.Injective (fun z : ℕ × ℕ => p z.1 z.2))
    (hl : Function.Injective (fun z : ℕ × ℕ => l z.1 z.2))
    (hsep : ∀ x y a b, p x y ≠ l a b)
    (hpn : ∀ x y, ‖p x y‖ = 1) (hln : ∀ a b, ‖l a b‖ = 1)
    (hd : ∀ a x b, dist (p x (a*x+b)) (l a b) = Real.sqrt 2)
    (m : ℕ) :
    ∃ S : Finset V, S.card = 3*m^3 ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
      ∃ edges : Finset (V × V), edges.card = m^4 ∧
        (∀ uv ∈ edges, uv.1 ∈ S ∧ uv.2 ∈ S ∧ dist uv.1 uv.2 = Real.sqrt 2) ∧
        (∀ u v, (u,v) ∈ edges → (v,u) ∉ edges) := by
  classical
  let P := ((range m) ×ˢ (range (2*m^2))).image (fun z => p z.1 z.2)
  let L := ((range m) ×ˢ (range (m^2))).image (fun z => l z.1 z.2)
  let T := ((range m) ×ˢ (range m)) ×ˢ (range (m^2))
  let e : (ℕ × ℕ) × ℕ → V × V := fun z =>
    (p z.1.2 (z.1.1*z.1.2+z.2), l z.1.1 z.2)
  have hinj : Function.Injective e := by
    intro u v huv
    have h₁ := hp (a₁ := (u.1.2, u.1.1*u.1.2+u.2)) (a₂ := (v.1.2, v.1.1*v.1.2+v.2)) (show p u.1.2 (u.1.1*u.1.2+u.2) = p v.1.2 (v.1.1*v.1.2+v.2) from congrArg Prod.fst huv)
    have h₂ := hl (a₁ := (u.1.1,u.2)) (a₂ := (v.1.1,v.2)) (show l u.1.1 u.2 = l v.1.1 v.2 from congrArg Prod.snd huv)
    have hx := congrArg Prod.fst h₁
    have ha := congrArg Prod.fst h₂
    have hb := congrArg Prod.snd h₂
    exact Prod.ext (Prod.ext ha hx) hb
  have hdis : Disjoint P L := by
    apply disjoint_left.mpr
    intro v hvp hvl
    obtain ⟨⟨x,y⟩, _, rfl⟩ := mem_image.mp hvp
    obtain ⟨⟨a,b⟩, _, hab⟩ := mem_image.mp hvl
    exact hsep x y a b hab.symm
  have hcP : P.card = 2*m^3 := by
    rw [card_image_of_injective _ hp, card_product, card_range, card_range]
    ring
  have hcL : L.card = m^3 := by
    rw [card_image_of_injective _ hl, card_product, card_range, card_range]
    ring
  refine ⟨P ∪ L, ?_, ?_, T.image e, ?_, ?_, ?_⟩
  · rw [card_union_of_disjoint hdis, hcP, hcL]
    omega
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨⟨x,y⟩, _, rfl⟩ := mem_image.mp hv
      exact hpn x y
    · obtain ⟨⟨a,b⟩, _, rfl⟩ := mem_image.mp hv
      exact hln a b
  · rw [card_image_of_injective _ hinj]
    simp only [T, card_product, card_range]
    ring
  · intro uv huv
    obtain ⟨⟨⟨a,x⟩,b⟩, hz, rfl⟩ := mem_image.mp huv
    have hz' : a < m ∧ x < m ∧ b < m^2 := by simpa [T, and_assoc] using hz
    have hax : a*x+b < 2*m^2 := by
      have hxle : x ≤ m := Nat.le_of_lt hz'.2.1
      have hale : a ≤ m := Nat.le_of_lt hz'.1
      have hh : a*x ≤ m*m := Nat.mul_le_mul hale hxle
      nlinarith [hz'.2.2]
    refine ⟨mem_union_left _ ?_, mem_union_right _ ?_, hd a x b⟩
    · apply mem_image.mpr
      exact ⟨(x,a*x+b), by simpa using And.intro hz'.2.1 hax, rfl⟩
    · apply mem_image.mpr
      exact ⟨(a,b), by simpa using And.intro hz'.1 hz'.2.2, rfl⟩
  · intro u v huv hvu
    obtain ⟨⟨⟨a,x⟩,b⟩, _, hz⟩ := mem_image.mp huv
    obtain ⟨⟨⟨c,y⟩,d⟩, _, hw⟩ := mem_image.mp hvu
    have hv := congrArg Prod.snd hz
    have hw' := congrArg Prod.fst hw
    exact hsep y (c*y+d) a b (hw'.trans hv.symm)

/-- A unit-sphere configuration of `3*m^3` points with `m^4` distinct
unoriented incidences, represented by consistently oriented pairs. -/
theorem sphere_grid (m : ℕ) :
    ∃ S : Finset E, S.card = 3*m^3 ∧ (∀ v ∈ S, ‖v‖ = 1) ∧
      ∃ edges : Finset (E × E), edges.card = m^4 ∧
        (∀ uv ∈ edges, uv.1 ∈ S ∧ uv.2 ∈ S ∧ dist uv.1 uv.2 = Real.sqrt 2) ∧
        (∀ u v, (u,v) ∈ edges → (v,u) ∉ edges) := by
  apply grid_construction
    (fun x y => point (x : ℝ) (y : ℝ))
    (fun a b => line (a : ℝ) (b : ℝ))
  · intro u v h
    have hh := point_injective (a₁ := ((u.1 : ℝ),(u.2 : ℝ)))
      (a₂ := ((v.1 : ℝ),(v.2 : ℝ))) h
    exact Prod.ext (Nat.cast_injective (congrArg Prod.fst hh))
      (Nat.cast_injective (congrArg Prod.snd hh))
  · intro u v h
    have hh := line_injective (a₁ := ((u.1 : ℝ),(u.2 : ℝ)))
      (a₂ := ((v.1 : ℝ),(v.2 : ℝ))) h
    exact Prod.ext (Nat.cast_injective (congrArg Prod.fst hh))
      (Nat.cast_injective (congrArg Prod.snd hh))
  · intro x y a b
    exact point_ne_line _ _ _ _ (Nat.cast_nonneg y)
  · intro x y
    exact point_norm _ _
  · intro a b
    exact line_norm _ _
  · intro a x b
    apply incidence_dist
    push_cast
    rfl

end JSP000492
