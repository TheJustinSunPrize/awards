import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FCC

open Finset

/-- The two possibilities for adjacent coordinates in opposite parity classes. -/
def Step {m : ℕ} (i j : Fin m) : Prop := i.val = j.val ∨ i.val = j.val + 1

instance {m : ℕ} : DecidableRel (@Step m) := fun i j =>
  inferInstanceAs (Decidable (i.val = j.val ∨ i.val = j.val + 1))

def stepEquiv (m : ℕ) : {p : Fin m × Fin m // Step p.1 p.2} ≃ Fin (2 * m - 1) where
  toFun p := ⟨p.1.1.val + p.1.2.val, by
    have hi := p.1.1.isLt
    have hj := p.1.2.isLt
    rcases p.2 with h | h <;> omega⟩
  invFun k := ⟨(⟨(k.val + 1) / 2, by have hk := k.isLt; omega⟩,
    ⟨k.val / 2, by have hk := k.isLt; omega⟩), by
      dsimp [Step]
      omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp
    · rcases p.2 with h | h <;> omega
    · rcases p.2 with h | h <;> omega
  right_inv k := by
    apply Fin.ext
    dsimp
    omega

theorem step_count (m : ℕ) :
    ((univ : Finset (Fin m × Fin m)).filter fun p => Step p.1 p.2).card =
      2 * m - 1 := by
  classical
  simpa [Fintype.card_subtype] using Fintype.card_congr (stepEquiv m)

theorem step_flip_count (m : ℕ) :
    ((univ : Finset (Fin m × Fin m)).filter fun p => Step p.2 p.1).card =
      2 * m - 1 := by
  classical
  let e : {p : Fin m × Fin m // Step p.2 p.1} ≃ {p : Fin m × Fin m // Step p.1 p.2} :=
    { toFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      invFun := fun p => ⟨(p.1.2, p.1.1), p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype] using Fintype.card_congr (e.trans (stepEquiv m))

theorem eq_pair_count (m : ℕ) :
    ((univ : Finset (Fin m × Fin m)).filter fun p => p.1 = p.2).card = m := by
  classical
  let e : {p : Fin m × Fin m // p.1 = p.2} ≃ Fin m :=
    { toFun := fun p => p.1.1
      invFun := fun i => ⟨(i, i), rfl⟩
      left_inv := by rintro ⟨⟨i,j⟩,h⟩; change i = j at h; subst j; rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

theorem product_relation_count {m : ℕ}
    (R S T : Fin m → Fin m → Prop)
    [DecidableRel R] [DecidableRel S] [DecidableRel T] :
    ((univ : Finset ((Fin m × Fin m × Fin m) × (Fin m × Fin m × Fin m))).filter
      fun p => R p.1.1 p.2.1 ∧ S p.1.2.1 p.2.2.1 ∧ T p.1.2.2 p.2.2.2).card =
    ((univ : Finset (Fin m × Fin m)).filter fun p => R p.1 p.2).card *
    ((univ : Finset (Fin m × Fin m)).filter fun p => S p.1 p.2).card *
    ((univ : Finset (Fin m × Fin m)).filter fun p => T p.1 p.2).card := by
  classical
  let e : {p : (Fin m × Fin m × Fin m) × (Fin m × Fin m × Fin m) //
      R p.1.1 p.2.1 ∧ S p.1.2.1 p.2.2.1 ∧ T p.1.2.2 p.2.2.2} ≃
      {p : Fin m × Fin m // R p.1 p.2} ×
      {p : Fin m × Fin m // S p.1 p.2} ×
      {p : Fin m × Fin m // T p.1 p.2} :=
    { toFun := fun p =>
        (⟨(p.1.1.1, p.1.2.1), p.2.1⟩,
         ⟨(p.1.1.2.1, p.1.2.2.1), p.2.2.1⟩,
         ⟨(p.1.1.2.2, p.1.2.2.2), p.2.2.2⟩)
      invFun := fun p =>
        ⟨((p.1.1.1, p.2.1.1.1, p.2.2.1.1),
          (p.1.1.2, p.2.1.1.2, p.2.2.1.2)), p.1.2, p.2.1.2, p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype, Nat.mul_assoc] using Fintype.card_congr e

theorem int_mul_pred_nonneg (a : ℤ) : 0 ≤ a * (a - 1) := by
  by_cases h : a ≤ 0
  · nlinarith [sq_nonneg a]
  · have h' : 1 ≤ a := by omega
    nlinarith [sq_nonneg (a - 1)]

theorem even_odd_odd_square_iff (a b c : ℤ) :
    (2 * a) ^ 2 + (2 * b - 1) ^ 2 + (2 * c - 1) ^ 2 = 2 ↔
      a = 0 ∧ (b = 0 ∨ b = 1) ∧ (c = 0 ∨ c = 1) := by
  constructor
  · intro h
    have hb := int_mul_pred_nonneg b
    have hc := int_mul_pred_nonneg c
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
    have hb0 : b * (b - 1) = 0 := by nlinarith [sq_nonneg a]
    have hc0 : c * (c - 1) = 0 := by nlinarith [sq_nonneg a]
    refine ⟨sq_eq_zero_iff.mp ha, ?_, ?_⟩
    · rcases mul_eq_zero.mp hb0 with h | h
      · exact Or.inl h
      · right; omega
    · rcases mul_eq_zero.mp hc0 with h | h
      · exact Or.inl h
      · right; omega
  · rintro ⟨rfl, hb, hc⟩
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

theorem int_diff_zero_iff {m : ℕ} (i j : Fin m) :
    (i.val : ℤ) - j.val = 0 ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; omega
  · intro h; subst j; simp

theorem int_diff_step_iff {m : ℕ} (i j : Fin m) :
    ((i.val : ℤ) - j.val = 0 ∨ (i.val : ℤ) - j.val = 1) ↔ Step i j := by
  simp only [Step]
  omega

end FCC
