import FCC.Basic
import FCC.CountCore

namespace FCC

open Finset

theorem contact_01 {m : ℕ} (u v : Cell m) :
    Contact (0, u) (1, v) ↔
      u.1 = v.1 ∧ Step u.2.1 v.2.1 ∧ Step u.2.2 v.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.1 : ℤ) - v.1) ((u.2.1 : ℤ) - v.2.1) ((u.2.2 : ℤ) - v.2.2)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

theorem contact_02 {m : ℕ} (u v : Cell m) :
    Contact (0, u) (2, v) ↔
      Step u.1 v.1 ∧ u.2.1 = v.2.1 ∧ Step u.2.2 v.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.2.1 : ℤ) - v.2.1) ((u.1 : ℤ) - v.1) ((u.2.2 : ℤ) - v.2.2)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  rw [and_left_comm] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

theorem contact_03 {m : ℕ} (u v : Cell m) :
    Contact (0, u) (3, v) ↔
      Step u.1 v.1 ∧ Step u.2.1 v.2.1 ∧ u.2.2 = v.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.2.2 : ℤ) - v.2.2) ((u.1 : ℤ) - v.1) ((u.2.1 : ℤ) - v.2.1)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  rw [and_comm (a := u.2.2 = v.2.2), and_assoc] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

theorem contact_12 {m : ℕ} (u v : Cell m) :
    Contact (1, u) (2, v) ↔
      Step u.1 v.1 ∧ Step v.2.1 u.2.1 ∧ u.2.2 = v.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.2.2 : ℤ) - v.2.2) ((u.1 : ℤ) - v.1) ((v.2.1 : ℤ) - u.2.1)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  rw [and_comm (a := u.2.2 = v.2.2), and_assoc] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

theorem contact_13 {m : ℕ} (u v : Cell m) :
    Contact (1, u) (3, v) ↔
      Step u.1 v.1 ∧ u.2.1 = v.2.1 ∧ Step v.2.2 u.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.2.1 : ℤ) - v.2.1) ((u.1 : ℤ) - v.1) ((v.2.2 : ℤ) - u.2.2)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  rw [and_left_comm] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

theorem contact_23 {m : ℕ} (u v : Cell m) :
    Contact (2, u) (3, v) ↔
      u.1 = v.1 ∧ Step u.2.1 v.2.1 ∧ Step v.2.2 u.2.2 := by
  have h := even_odd_odd_square_iff
    ((u.1 : ℤ) - v.1) ((u.2.1 : ℤ) - v.2.1) ((v.2.2 : ℤ) - u.2.2)
  rw [int_diff_zero_iff, int_diff_step_iff, int_diff_step_iff] at h
  convert h using 1; simp [Contact, sqDist, coord, cellCoord, offset]; ring_nf

def classPairCount (m : ℕ) (a b : Fin 4) : ℕ :=
  ((univ : Finset (Cell m × Cell m)).filter fun p => Contact (a,p.1) (b,p.2)).card

theorem classPairCount_01 (m : ℕ) : classPairCount m 0 1 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_01]
  rw [product_relation_count, eq_pair_count, step_count]
  ring

theorem classPairCount_02 (m : ℕ) : classPairCount m 0 2 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_02]
  rw [product_relation_count, eq_pair_count, step_count]
  ring

theorem classPairCount_03 (m : ℕ) : classPairCount m 0 3 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_03]
  rw [product_relation_count, eq_pair_count, step_count]
  ring

theorem classPairCount_12 (m : ℕ) : classPairCount m 1 2 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_12]
  rw [product_relation_count Step (fun i j => Step j i) Eq,
    eq_pair_count, step_count, step_flip_count]
  ring

theorem classPairCount_13 (m : ℕ) : classPairCount m 1 3 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_13]
  rw [product_relation_count Step Eq (fun i j => Step j i),
    eq_pair_count, step_count, step_flip_count]
  ring

theorem classPairCount_23 (m : ℕ) : classPairCount m 2 3 = m * (2*m-1)^2 := by
  simp only [classPairCount, contact_23]
  rw [product_relation_count Eq Step (fun i j => Step j i),
    eq_pair_count, step_count, step_flip_count]
  ring

theorem contactPairs_card_sum (m : ℕ) :
    (contactPairs m).card = ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then classPairCount m a b else 0 := by
  classical
  let t : Finset ((Fin 4 × Fin 4) × (Cell m × Cell m)) :=
    univ.filter fun p => p.1.1 < p.1.2 ∧ Contact (p.1.1,p.2.1) (p.1.2,p.2.2)
  have hc : (contactPairs m).card = t.card := by
    apply card_bij (fun p _ => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
    · intro p hp
      simpa [t, contactPairs] using hp
    · rintro ⟨⟨a,u⟩,⟨b,v⟩⟩ _ ⟨⟨a',u'⟩,⟨b',v'⟩⟩ _ h
      simpa only [Prod.mk.injEq, and_and_and_comm] using h
    · rintro ⟨⟨a,b⟩,⟨u,v⟩⟩ hp
      refine ⟨((a,u),(b,v)), ?_, rfl⟩
      simpa [t, contactPairs] using hp
  rw [hc]
  have hp : t.card = ∑ ab : Fin 4 × Fin 4,
      ((univ : Finset (Cell m × Cell m)).filter
        fun p => ab.1 < ab.2 ∧ Contact (ab.1,p.1) (ab.2,p.2)).card := by
    simp only [t, card_filter, Fintype.sum_prod_type]
  rw [hp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases h : a < b <;> simp [h, classPairCount]

theorem contactPairs_card (m : ℕ) :
    (contactPairs m).card = 6 * m * (2*m-1)^2 := by
  rw [contactPairs_card_sum]
  simp only [Fin.sum_univ_succ]
  norm_num [Fin.lt_def, Fin.ext_iff, Fin.val_succ,
    show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
    classPairCount_01, classPairCount_02, classPairCount_03,
    classPairCount_12, classPairCount_13, classPairCount_23]
  ring

end FCC
