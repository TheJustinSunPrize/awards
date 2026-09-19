import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory22757 (t x_0_2 x_0_6 x_2_6 x_6_7 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22758 (t x_0_6 x_5_6 x_5_7 x_6_7 x_6_8 x_7_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22772 (x_3_4 x_3_6 x_4_8 x_6_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≤ 0)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22774 (t x_0_2 x_0_6 x_2_3 x_2_5 x_2_6 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_2_3) + x_2_5) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22777 (x_0_6 x_1_6 x_4_6 : ℝ) : (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_0_6 + ((-1) * x_4_6)) ≥ 0) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22784 (t x_0_7 x_3_4 x_4_5 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22788 (t x_3_4 x_4_8 x_4_9 x_5_9 x_8_10 x_8_9 : ℝ) : (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22789 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22791 (t x_1_3 x_3_6 x_3_7 x_3_8 x_6_7 x_6_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_9) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22796 (t x_0_8 x_3_4 x_4_7 x_4_8 x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22803 (t x_0_3 x_0_7 x_1_3 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22805 (t x_0_3 x_0_5 x_1_5 x_3_7 x_4_7 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_5) ≥ 1)) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory22815 (t x_1_4 x_1_5 x_2_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22817 (t x_0_1 x_0_5 x_1_4 x_4_6 x_5_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22827 (t x_0_8 x_1_3 x_3_6 x_3_8 x_4_6 x_6_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22828 (t x_0_1 x_0_3 x_1_2 x_2_4 x_3_6 x_3_7 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory22829 (t x_0_4 x_2_3 x_3_4 x_4_5 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22831 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_6 : ℝ) : (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22832 (t x_0_3 x_3_7 x_4_6 x_4_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_6_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22833 (x_0_4 x_0_9 x_2_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_4_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22836 (x_1_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22841 (t x_0_4 x_0_7 x_1_3 x_3_4 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory22842 (t x_0_1 x_0_8 x_1_2 x_1_8 x_8_10 : ℝ) : (¬ ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22844 (t x_0_1 x_0_7 x_1_2 x_1_3 x_1_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22847 (t x_0_4 x_3_4 x_4_7 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22848 (t x_0_3 x_0_7 x_1_3 x_2_7 x_3_4 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory22851 (t x_0_1 x_0_2 x_1_2 x_1_4 x_2_6 : ℝ) : (¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22857 (t x_0_4 x_2_4 x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22858 (x_1_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22861 (x_1_3 x_1_4 x_1_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_1_7)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22868 (t x_0_3 x_2_3 x_2_6 x_3_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22869 (t x_4_7 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22870 (t x_0_3 x_0_5 x_1_3 x_1_6 x_3_5 x_3_6 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory22872 (t x_0_4 x_1_3 x_3_4 x_3_7 x_3_8 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22874 (t x_0_6 x_0_9 x_4_6 x_5_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22875 (t x_0_4 x_2_4 x_4_6 x_4_8 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22877 (t x_2_7 x_2_8 x_5_7 x_7_8 x_8_9 : ℝ) : (¬ ((t + x_2_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22889 (t x_0_2 x_1_5 x_2_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_5 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22891 (t x_0_5 x_4_6 x_5_6 x_5_7 x_5_8 x_6_7 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22894 (t x_0_3 x_2_3 x_2_8 x_3_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22896 (t x_0_4 x_1_2 x_2_4 x_2_5 x_4_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22905 (t x_2_5 x_2_8 x_4_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22906 (t x_0_2 x_0_3 x_0_4 x_3_5 x_4_7 x_5_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_8_9) + x_8_10) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory22907 (t x_0_1 x_1_2 x_1_3 x_2_3 x_3_7 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22909 (t x_0_4 x_1_3 x_3_4 x_4_5 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22912 (x_2_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22917 (x_2_7 x_4_7 x_5_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_2_7 + ((-1) * x_5_7)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22924 (x_0_5 x_1_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22925 (t x_0_6 x_1_2 x_2_3 x_2_6 x_6_9 x_9_10 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22926 (x_0_5 x_1_5 x_4_5 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_4_5)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22928 (t x_0_1 x_0_4 x_1_3 x_1_4 x_1_5 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22932 (t x_2_3 x_3_4 x_3_7 x_5_7 x_7_9 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22933 (t x_0_4 x_0_7 x_3_4 x_4_5 x_5_7 x_7_9 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22941 (t x_3_8 x_7_8 x_8_9 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22942 (x_1_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22943 (t x_0_5 x_1_2 x_2_5 x_2_6 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22947 (t x_2_3 x_2_6 x_3_4 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≤ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22953 (x_1_5 x_1_6 x_1_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_1_9)) ≤ 0)) ∨ ((x_1_5 + ((-1) * x_1_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22963 (t x_1_4 x_3_4 x_4_7 : ℝ) : ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22966 (t x_0_1 x_1_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory22973 (x_0_5 x_1_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22975 (t x_1_5 x_3_5 x_5_8 x_5_9 x_9_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22977 (t x_0_4 x_0_6 x_1_4 x_4_6 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_1_4) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22982 (t x_0_1 x_0_5 x_1_6 x_3_5 x_5_8 x_5_9 x_6_7 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_5) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory22986 (t x_1_3 x_1_7 x_3_4 x_3_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory22989 (t x_0_3 x_3_6 x_4_5 x_5_6 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory22991 (t x_0_1 x_0_4 x_1_2 x_2_6 x_4_5 x_5_8 x_6_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory22992 (x_0_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22995 (x_0_6 x_1_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory22996 (x_0_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory22997 (t x_0_2 x_0_3 x_2_6 x_3_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23002 (t x_0_2 x_0_3 x_0_5 x_1_2 x_2_5 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23010 (t x_3_5 x_4_5 x_5_8 x_5_9 x_9_10 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23017 (t x_0_1 x_0_2 x_1_2 x_2_3 x_2_7 x_3_7 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23019 (t x_1_2 x_2_4 x_2_6 x_3_4 x_4_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23020 (t x_0_1 x_0_3 x_1_3 x_3_7 x_3_8 x_8_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23023 (x_1_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23024 (t x_2_4 x_2_6 x_3_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23028 (t x_1_2 x_2_4 x_2_7 x_4_7 x_4_9 : ℝ) : (¬ ((t + x_4_7 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23031 (t x_3_4 x_3_5 x_3_7 : ℝ) : (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_3_5) + x_3_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23038 (t x_0_4 x_0_7 x_3_4 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23047 (t x_3_8 x_5_6 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((t + x_3_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23062 (t x_0_8 x_1_8 x_5_8 x_6_7 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23064 (t x_0_2 x_0_4 x_1_2 x_2_4 x_2_6 x_4_5 x_5_9 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_5_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23066 (x_1_8 x_3_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23068 (t x_0_5 x_1_5 x_4_5 x_5_6 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23077 (t x_2_4 x_3_4 x_3_5 x_3_6 x_4_6 x_6_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23081 (t x_0_2 x_0_4 x_1_2 x_2_4 x_2_6 x_4_5 x_5_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((t + x_5_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23086 (x_1_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) ∨ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23097 (t x_0_3 x_0_7 x_1_3 x_3_5 x_3_7 x_5_8 x_7_9 x_8_10 x_9_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23098 (t x_0_5 x_0_7 x_3_7 x_5_6 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_7) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23099 (t x_0_1 x_0_2 x_0_8 x_2_7 x_2_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23101 (t x_1_7 x_3_7 x_5_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23104 (x_1_3 x_2_3 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23108 (t x_0_6 x_0_7 x_5_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_6_7) + x_6_9) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23111 (x_1_2 x_2_3 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23115 (t x_0_1 x_0_2 x_1_4 x_2_6 x_2_8 x_4_5 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23118 (x_1_3 x_3_6 x_3_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23121 (x_2_5 x_2_8 x_5_9 x_8_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_2_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23122 (t x_0_1 x_0_2 x_1_4 x_2_7 x_2_9 x_4_8 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23125 (t x_0_1 x_0_2 x_1_3 x_2_4 x_3_8 x_4_7 x_7_9 x_8_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23127 (t x_0_6 x_2_6 x_6_7 x_6_9 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_2_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23130 (x_5_6 x_5_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23131 (x_5_6 x_5_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23137 (t x_0_6 x_1_2 x_1_6 x_2_3 x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23139 (t x_0_2 x_0_4 x_1_2 x_1_7 x_2_4 x_2_7 x_4_5 x_5_7 x_5_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((t + x_5_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23146 (t x_2_4 x_3_6 x_4_8 x_4_9 x_6_7 x_6_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23148 (x_0_6 x_1_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23159 (t x_0_6 x_0_7 x_1_3 x_3_6 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23165 (t x_0_2 x_2_4 x_2_5 x_5_6 x_6_9 : ℝ) : (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23168 (t x_0_7 x_5_6 x_5_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23172 (t x_1_7 x_1_8 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_1_7) + x_3_7) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23174 (t x_0_1 x_0_2 x_0_4 x_1_2 x_1_3 x_1_6 x_4_8 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23175 (t x_2_7 x_2_8 x_3_7 x_5_7 x_6_7 x_7_8 x_7_9 x_8_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23177 (t x_0_6 x_3_6 x_4_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23179 (x_0_1 x_1_6 x_1_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ ((x_0_1 + ((-1) * x_1_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23182 (t x_0_7 x_2_7 x_3_7 x_7_8 x_7_9 x_8_10 x_8_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23185 (t x_3_6 x_4_8 x_6_8 x_6_9 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23188 (t x_2_5 x_3_6 x_5_6 x_5_9 x_6_7 x_6_9 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23193 (t x_0_7 x_1_6 x_1_7 x_2_6 x_6_7 x_6_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23194 (t x_0_3 x_0_7 x_1_8 x_3_5 x_5_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_1_8) + x_6_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_7) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23200 (x_4_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23201 (t x_1_7 x_1_8 x_2_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23203 (t x_0_4 x_0_7 x_1_4 x_3_7 x_4_5 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23209 (x_0_1 x_1_7 x_1_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23210 (t x_0_1 x_1_2 x_2_5 x_5_7 x_7_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23211 (t x_0_2 x_0_3 x_0_7 x_1_2 x_1_3 x_2_7 x_3_5 x_5_6 x_6_9 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23216 (t x_0_1 x_0_3 x_1_7 x_2_7 x_3_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23220 (t x_0_2 x_0_3 x_0_4 x_0_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23223 (t x_0_1 x_0_2 x_0_3 x_0_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1)) ∨ ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23231 (t x_0_2 x_0_3 x_0_4 x_0_5 x_1_2 x_1_3 x_2_4 x_3_6 x_4_7 x_4_9 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory23233 (t x_0_2 x_2_3 x_3_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23235 (t x_0_2 x_0_3 x_0_4 x_1_2 x_1_3 x_2_4 x_3_6 x_3_8 x_4_7 x_4_8 x_4_9 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory23237 (t x_0_2 x_2_4 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23250 (t x_0_2 x_0_3 x_0_4 x_0_6 x_1_2 x_1_3 x_2_5 x_3_6 x_4_5 x_5_7 x_6_8 x_6_9 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory23255 (x_0_4 x_0_5 x_4_9 x_5_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23256 (t x_0_2 x_0_3 x_0_4 x_2_5 x_3_8 x_4_5 x_5_7 x_7_10 x_8_9 x_9_10 : ℝ) : (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_7_10) + x_9_10) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23265 (t x_0_4 x_0_7 x_1_2 x_1_7 x_2_4 x_2_5 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_2_4) + x_2_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23266 (t x_0_1 x_0_7 x_1_2 x_1_4 x_1_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23268 (t x_0_6 x_1_2 x_2_6 x_2_7 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23275 (t x_0_1 x_0_4 x_1_2 x_1_3 x_1_4 x_1_7 x_2_4 x_4_5 x_4_9 x_5_7 x_7_9 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory23277 (t x_0_1 x_0_4 x_1_3 x_3_7 x_4_6 x_6_9 x_7_10 x_9_10 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_7_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23281 (x_1_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≤ 0)) ∨ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23282 (t x_2_5 x_3_5 x_5_7 x_5_8 x_8_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_2_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23283 (t x_0_2 x_0_3 x_1_2 x_1_3 x_2_7 x_3_4 x_4_8 x_7_9 x_8_10 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23285 (t x_0_4 x_0_5 x_0_6 x_1_2 x_1_4 x_1_5 x_3_6 x_5_9 x_6_8 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory23287 (t x_0_3 x_1_2 x_2_3 x_3_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23292 (t x_0_1 x_0_3 x_1_4 x_3_7 x_3_8 x_4_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23293 (t x_0_1 x_0_5 x_1_4 x_4_6 x_5_8 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_5) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23299 (t x_0_1 x_0_2 x_0_7 x_2_3 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23300 (t x_0_1 x_0_5 x_1_2 x_1_4 x_1_5 x_1_8 x_5_9 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23303 (t x_1_2 x_2_7 x_2_8 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_7_8) + x_7_9) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23307 (t x_0_3 x_0_5 x_1_2 x_1_3 x_1_5 x_2_5 x_3_4 x_4_6 x_5_7 x_5_8 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23314 (t x_0_3 x_0_5 x_1_2 x_1_3 x_1_5 x_2_5 x_3_4 x_4_6 x_5_7 x_5_8 x_6_7 x_6_8 : ℝ) : (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory23316 (t x_2_7 x_2_8 x_4_7 x_7_8 x_7_9 x_8_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23318 (t x_0_1 x_0_2 x_0_5 x_1_2 x_1_3 x_1_8 x_5_6 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23320 (t x_0_3 x_0_5 x_1_2 x_1_3 x_1_5 x_2_5 x_3_4 x_4_8 x_5_7 x_5_9 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_5_9) + x_8_9) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23324 (t x_0_1 x_0_2 x_0_5 x_1_2 x_1_3 x_1_6 x_5_9 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory23326 (t x_0_1 x_1_3 x_1_9 x_3_5 x_3_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23333 (t x_0_3 x_2_3 x_3_4 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23340 (t x_0_1 x_1_4 x_1_7 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23341 (t x_0_2 x_2_3 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23342 (t x_0_2 x_0_5 x_0_7 x_1_2 x_1_7 x_2_5 x_5_6 x_5_9 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_5_9) + x_8_9) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23344 (t x_1_2 x_1_6 x_2_3 x_2_4 x_2_6 x_6_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23345 (t x_0_2 x_0_4 x_2_5 x_4_6 x_5_9 x_6_8 x_8_10 x_9_10 : ℝ) : (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23348 (x_0_4 x_3_4 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23349 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23354 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23357 (x_3_4 x_3_5 x_4_8 x_5_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23359 (x_0_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23363 (t x_0_2 x_0_3 x_2_3 x_2_4 x_2_8 x_3_5 x_5_9 x_8_10 x_9_10 : ℝ) : (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23364 (t x_0_1 x_0_3 x_0_5 x_1_4 x_3_8 x_3_9 x_4_6 x_5_8 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23365 (t x_0_1 x_0_2 x_1_2 x_1_4 x_1_8 x_2_5 x_5_6 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23366 (t x_0_1 x_0_2 x_0_6 x_1_6 x_2_3 x_3_4 x_4_7 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23368 (t x_0_1 x_0_3 x_1_4 x_3_5 x_4_7 x_5_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23369 (t x_0_1 x_0_3 x_1_4 x_3_5 x_4_7 x_5_6 x_6_9 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23374 (t x_0_2 x_2_3 x_3_6 x_3_9 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≤ 0)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23376 (t x_0_1 x_0_3 x_1_4 x_3_5 x_4_7 x_5_8 x_7_10 x_8_10 : ℝ) : (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((t + x_7_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23378 (t x_0_1 x_0_2 x_1_3 x_2_5 x_3_8 x_5_6 x_6_9 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23380 (t x_0_1 x_0_3 x_1_4 x_3_5 x_4_9 x_5_6 x_6_10 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23381 (t x_0_2 x_0_4 x_0_7 x_1_2 x_1_4 x_2_5 x_5_6 x_6_9 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory23385 (t x_0_5 x_2_3 x_3_5 x_3_6 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23389 (t x_0_1 x_0_2 x_0_4 x_2_3 x_3_6 x_4_8 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_2)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory23404 (x_0_4 x_0_6 x_1_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory23405 (t x_1_4 x_1_7 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + x_4_6 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23408 (t x_0_7 x_0_8 x_1_6 x_1_8 x_4_6 x_6_7 x_8_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23419 (x_4_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≤ 0)) ∨ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23421 (t x_0_4 x_1_4 x_1_6 x_1_7 x_4_5 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_1_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23429 (t x_0_6 x_0_8 x_1_6 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23435 (t x_3_8 x_5_6 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_8) + x_6_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23444 (t x_0_5 x_2_5 x_4_5 x_5_6 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory23450 (x_0_1 x_0_4 x_0_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_0_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory23451 (t x_0_1 x_0_3 x_1_3 x_1_6 x_3_6 x_3_8 x_6_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory23453 (t x_0_3 x_0_6 x_3_4 x_3_6 x_3_7 x_6_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23473 (t x_0_1 x_0_6 x_1_3 x_1_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory23477 (x_1_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23486 (t x_0_4 x_1_4 x_4_6 x_4_9 x_9_10 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23489 (x_1_4 x_1_5 x_4_7 x_5_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory23491 (t x_2_4 x_3_4 x_3_6 x_4_5 x_4_6 x_6_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory23513 (x_0_1 x_0_4 x_1_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

end ElevenTheory
