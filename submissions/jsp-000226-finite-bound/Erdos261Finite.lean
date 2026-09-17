import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
Finite verification for Erdős 261 / JSP-000226.
The mathematical finite bound is due to Tengely, Ulas, and Zygadło (2020).
This file is a new formalization, not a claim of a new mathematical solution.
-/
namespace Erdos261Finite

def Represents (a r : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ j ∈ s, a < j) ∧
    (r : ℚ) / 2 ^ a = ∑ j ∈ s, (j : ℚ) / 2 ^ j

def advance (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + 1, if p.1 + 1 ≤ 2 * p.2 then 2 * p.2 - (p.1 + 1) else 2 * p.2)

def run : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | k + 1, p => run k (advance p)

theorem zero_represents (a : ℕ) : Represents a 0 := by
  refine ⟨∅, ?_, ?_⟩ <;> simp

theorem transfer (a r : ℕ) (hrep : Represents (advance (a, r)).1
    (advance (a, r)).2) : Represents a r := by
  simp only [advance] at hrep
  split_ifs at hrep with h
  · obtain ⟨s, hs, heq⟩ := hrep
    have hnot : a + 1 ∉ s := by intro hm; have := hs _ hm; omega
    refine ⟨insert (a + 1) s, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · omega
      · have := hs _ hj; omega
    · rw [Finset.sum_insert hnot, ← heq]
      rw [Nat.cast_sub h]
      push_cast
      rw [pow_succ]
      field_simp
      ring
  · obtain ⟨s, hs, heq⟩ := hrep
    refine ⟨s, ?_, ?_⟩
    · intro j hj; have := hs _ hj; omega
    · rw [← heq, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      field_simp

theorem run_transfer (k a r : ℕ)
    (hrep : Represents (run k (a, r)).1 (run k (a, r)).2) : Represents a r := by
  induction k generalizing a r with
  | zero => exact hrep
  | succ k ih =>
    apply transfer a r
    exact ih _ _ hrep

/-- A certificate segment is checked by the kernel by reducing `run`. -/
theorem segment (k a r b s : ℕ) (h : run k (a, r) = (b, s))
    (hrep : Represents b s) : Represents a r := by
  apply run_transfer k a r
  simpa only [h] using hrep

/-- The exact finite-decomposition property from the public problem statement. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ (t : ℕ), 2 ≤ t ∧ ∃ a : Fin t → ℕ,
  Function.Injective a ∧ (1 ≤ a) ∧
    (n : ℚ) / (2 ^ n : ℚ) = ∑ k, (a k : ℚ) / (2 ^ (a k) : ℚ)

theorem property_of_finset (n : ℕ) (s : Finset ℕ) (hc : 2 ≤ s.card)
    (hp : ∀ j ∈ s, 1 ≤ j)
    (he : (n : ℚ) / 2 ^ n = ∑ j ∈ s, (j : ℚ) / 2 ^ j) : Erdos261Prop n := by
  refine ⟨s.card, hc, s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).injective, ?_, ?_⟩
  · intro i
    exact hp _ (s.orderEmbOfFin_mem rfl i)
  · rw [he]
    conv_lhs => rw [← s.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]
    rfl

theorem property_of_tail (n : ℕ) (hn : 2 ≤ n)
    (hrep : Represents (n + 1) (n - 1)) : Erdos261Prop n := by
  obtain ⟨s, hs, he⟩ := hrep
  have hnot : n + 1 ∉ s := by intro hm; have := hs _ hm; omega
  have hne : s.Nonempty := by
    by_contra h
    have hem : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hem] at he
    simp only [Finset.sum_empty] at he
    have hpos : (0 : ℚ) < (n - 1 : ℕ) / (2 : ℚ) ^ (n + 1) := by
      have : 0 < n - 1 := by omega
      positivity
    rw [he] at hpos
    exact (lt_irrefl 0) hpos
  apply property_of_finset n (insert (n + 1) s)
  · rw [Finset.card_insert_of_notMem hnot]
    have := Finset.card_pos.mpr hne
    omega
  · intro j hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · omega
    · have := hs _ hj; omega
  · rw [Finset.sum_insert hnot, ← he, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem property_one : Erdos261Prop 1 := by
  apply property_of_finset 1 {3, 6, 8}
  · decide
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> decide
  · norm_num

end Erdos261Finite
