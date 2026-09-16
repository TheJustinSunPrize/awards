import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import Mathlib.Order.Filter.AtTopBot.Archimedean

namespace JSP000492

/-- The largest grid parameter whose three cubic blocks fit in `n` vertices. -/
def gridSize (n : ℕ) : ℕ := Nat.findGreatest (fun m => 3 * m ^ 3 ≤ n) n

theorem gridSize_fits (n : ℕ) : 3 * gridSize n ^ 3 ≤ n := by
  exact Nat.findGreatest_spec (P := fun m => 3 * m ^ 3 ≤ n) (m := 0) (by omega) (by simp)

theorem le_gridSize {k n : ℕ} (h : 3 * k ^ 3 ≤ n) : k ≤ gridSize n := by
  apply Nat.le_findGreatest (P := fun m => 3 * m ^ 3 ≤ n) ?_ h
  have hk : k ≤ k ^ 3 := by
    rcases k with _ | k
    · simp
    · exact le_self_pow (by omega) (by decide)
  omega

theorem lt_gridSize_next (n : ℕ) : n < 3 * (gridSize n + 1) ^ 3 := by
  by_contra h
  have hle : 3 * (gridSize n + 1) ^ 3 ≤ n := by omega
  have := le_gridSize hle
  omega

theorem gridSize_bound {n : ℕ} (h : 1 ≤ gridSize n) : n < 24 * gridSize n ^ 3 := by
  have hn := lt_gridSize_next n
  have hsq : (gridSize n + 1) ^ 3 ≤ (2 * gridSize n) ^ 3 := by
    exact Nat.pow_le_pow_left (show gridSize n + 1 ≤ 2 * gridSize n by omega) 3
  nlinarith

/-- For all large `n`, the explicit grid supplies at least `K*n` incidences. -/
theorem gridSize_many (K n : ℕ) (hn : 3 * (24 * K + 1) ^ 3 ≤ n) :
    K * n ≤ gridSize n ^ 4 := by
  have hm := le_gridSize hn
  have hb := gridSize_bound (n := n) (by omega)
  have h₁ : K * n ≤ K * (24 * gridSize n ^ 3) := Nat.mul_le_mul_left K hb.le
  have h₂ : K * 24 ≤ gridSize n := by omega
  have h₃ := Nat.mul_le_mul_right (gridSize n ^ 3) h₂
  nlinarith

/-- Integer-valued lower bound for the number of equal-distance pairs per vertex. -/
def quota (n : ℕ) : ℕ := gridSize n / 24

theorem quota_many (n : ℕ) : quota n * n ≤ gridSize n ^ 4 := by
  by_cases h : gridSize n = 0
  · simp [quota, h]
  have hb := gridSize_bound (n := n) (by omega)
  have h₁ := Nat.mul_le_mul_left (quota n) hb.le
  have h₂ : quota n * 24 ≤ gridSize n := Nat.div_mul_le_self _ _
  have h₃ := Nat.mul_le_mul_right (gridSize n ^ 3) h₂
  nlinarith

theorem quota_tendsto : Filter.Tendsto quota Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro K
  refine ⟨3 * (24 * K) ^ 3, ?_⟩
  intro n hn
  have h := le_gridSize hn
  dsimp [quota]
  omega

theorem quota_real_tendsto :
    Filter.Tendsto (fun n => (quota n : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_natCast_atTop_atTop.comp quota_tendsto

end JSP000492
