/-
JSP-000381: Primitive semiperfect numbers — Basic results

This file proves:
1. 6 is a semiperfect number (6 = 1 + 2 + 3)
2. 12 is a semiperfect number (12 = 1 + 2 + 3 + 6)
3. 20 is a semiperfect number (20 = 1 + 4 + 5 + 10)
4. 12 is NOT primitive semiperfect (6 | 12 and 6 is semiperfect)

References:
  [Er50] Erdős, 1950.
-/

import Mathlib

open Nat

/-- A semiperfect number: n equals the sum of some of its proper divisors -/
def IsSemiperfect (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ d ∈ s, d ∣ n ∧ d < n) ∧ s.sum id = n

/-- 6 is semiperfect: 6 = 1 + 2 + 3 -/
theorem six_semiperfect : IsSemiperfect 6 := by
  refine ⟨{1, 2, 3}, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · decide

/-- 12 is semiperfect: 12 = 1 + 2 + 3 + 6 -/
theorem twelve_semiperfect : IsSemiperfect 12 := by
  refine ⟨{1, 2, 3, 6}, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · decide

/-- 20 is semiperfect: 20 = 1 + 4 + 5 + 10 -/
theorem twenty_semiperfect : IsSemiperfect 20 := by
  refine ⟨{1, 4, 5, 10}, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  · decide

/-- A primitive semiperfect number: semiperfect with no semiperfect proper divisor -/
def IsPrimitiveSemiperfect (n : ℕ) : Prop :=
  IsSemiperfect n ∧ ∀ m : ℕ, m < n → m ∣ n → ¬ IsSemiperfect m

/-- 12 is NOT primitive semiperfect (6 | 12 and 6 is semiperfect) -/
theorem twelve_not_primitive : ¬ IsPrimitiveSemiperfect 12 := by
  intro h
  obtain ⟨_, hprim⟩ := h
  exact hprim 6 (by decide) (by decide) six_semiperfect
