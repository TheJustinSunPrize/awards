import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory7320 (x_2_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7321 (t x_0_2 x_2_3 x_3_8 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7322 (t x_0_2 x_0_3 x_3_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7323 (t x_0_3 x_2_3 x_3_6 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7324 (t x_1_3 x_3_5 x_5_6 x_6_7 x_7_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_7_10 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7325 (t x_0_1 x_1_3 x_1_8 x_3_8 x_8_9 : ℝ) : (¬ (x_3_8 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7327 (t x_0_3 x_3_6 x_5_6 x_6_10 x_6_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7329 (t x_0_1 x_1_4 x_1_9 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ (x_1_4 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7332 (t x_0_2 x_0_3 x_2_3 x_3_6 x_3_8 x_6_8 x_8_10 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7333 (t x_0_1 x_1_2 x_1_9 x_2_6 x_6_7 x_6_8 x_6_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7335 (t x_0_1 x_1_4 x_1_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7337 (t x_0_1 x_1_2 x_1_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7342 (t x_0_1 x_1_3 x_1_6 x_5_6 x_6_9 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7344 (t x_0_4 x_0_5 x_5_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7345 (t x_0_1 x_1_2 x_1_7 x_7_8 x_8_10 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ (x_8_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7348 (t x_2_3 x_3_5 x_3_9 x_4_5 x_5_8 x_5_9 : ℝ) : ((t + ((-1) * x_5_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ (x_3_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7351 (t x_1_6 x_1_7 x_4_7 x_4_8 x_6_8 x_7_10 x_8_9 : ℝ) : (¬ (x_1_6 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7353 (t x_0_2 x_2_3 x_3_8 x_4_8 x_8_10 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_4_8 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7354 (t x_0_2 x_2_3 x_3_4 x_4_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7357 (t x_0_1 x_1_3 x_1_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_3_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7358 (t x_0_8 x_3_4 x_4_6 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7360 (t x_0_1 x_1_2 x_1_4 x_3_4 x_4_7 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7361 (t x_0_1 x_1_2 x_1_3 x_3_4 x_4_5 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7362 (t x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7363 (t x_1_3 x_2_3 x_3_4 x_3_8 x_4_5 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7364 (t x_0_1 x_1_3 x_1_6 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7365 (t x_3_5 x_3_8 x_5_7 : ℝ) : ((t + x_3_5 + ((-1) * x_3_8)) ≥ 1) ∨ ((t + ((-1) * x_3_8)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7366 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_6 x_6_7 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7368 (t x_0_3 x_2_3 x_3_4 x_3_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7369 (t x_0_3 x_2_3 x_2_9 x_3_7 x_3_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7370 (t x_2_3 x_3_5 x_3_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7371 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_8 x_8_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_8_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7372 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7375 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_6 x_4_6 x_6_8 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7376 (t x_1_2 x_1_9 x_2_3 x_3_6 x_3_9 x_9_10 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7380 (t x_0_2 x_2_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7381 (t x_0_2 x_2_5 x_4_5 x_5_7 x_5_8 : ℝ) : (¬ (x_5_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7383 (t x_0_2 x_2_4 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7384 (t x_0_3 x_1_3 x_3_5 x_3_6 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7385 (t x_0_3 x_1_3 x_2_3 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7387 (t x_0_3 x_3_5 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7390 (t x_1_4 x_3_4 x_4_5 x_4_7 x_4_8 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7393 (t x_0_5 x_1_2 x_2_3 x_2_5 x_3_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7397 (t x_0_2 x_2_6 x_5_6 x_6_10 x_6_9 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7398 (t x_0_1 x_1_7 x_4_7 x_7_10 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7399 (t x_1_5 x_5_7 x_6_7 x_7_10 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7400 (t x_0_3 x_3_6 x_6_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7401 (t x_1_2 x_2_3 x_2_4 x_3_4 x_4_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7403 (t x_0_2 x_2_4 x_4_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7406 (t x_1_4 x_2_4 x_3_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_2_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7408 (t x_0_4 x_1_2 x_2_4 x_2_6 x_3_4 x_4_8 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7409 (t x_1_4 x_3_4 x_4_6 x_4_8 x_4_9 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7411 (t x_0_2 x_2_3 x_2_6 x_3_6 x_6_9 x_9_10 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7416 (t x_3_7 x_7_8 x_7_9 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_3_7)) ≤ 0) ∨ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7418 (t x_0_5 x_1_5 x_3_5 x_5_6 x_5_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7419 (t x_0_1 x_0_4 x_1_4 x_4_7 x_4_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7420 (t x_0_4 x_1_4 x_4_7 x_4_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7423 (t x_0_5 x_1_5 x_2_3 x_3_5 x_3_7 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_3_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7424 (t x_0_7 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7426 (t x_0_3 x_2_3 x_3_6 x_3_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7427 (t x_0_1 x_0_2 x_1_2 x_1_3 x_2_3 x_2_6 x_3_4 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7428 (t x_0_2 x_0_4 x_2_4 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7432 (t x_0_2 x_2_4 x_4_8 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7433 (t x_0_3 x_2_3 x_3_6 x_3_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7436 (t x_0_3 x_3_5 x_3_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7438 (t x_0_3 x_3_5 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7439 (x_1_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7442 (t x_3_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7444 (t x_0_4 x_4_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7445 (t x_0_1 x_1_6 x_4_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7449 (t x_0_3 x_2_3 x_3_4 x_3_5 x_5_8 : ℝ) : (¬ (x_5_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7450 (t x_0_2 x_2_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7451 (t x_0_3 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7452 (t x_0_1 x_1_4 x_1_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7454 (t x_0_6 x_1_3 x_3_6 x_6_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ ((t + ((-1) * x_8_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7455 (t x_0_5 x_4_7 x_5_7 x_7_10 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7456 (t x_1_7 x_3_5 x_5_7 x_5_9 x_7_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ ((t + ((-1) * x_1_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7458 (t x_0_5 x_4_5 x_5_6 x_5_7 x_6_9 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7459 (t x_0_3 x_3_4 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7460 (t x_0_3 x_3_4 x_4_7 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7461 (t x_0_1 x_1_9 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7463 (t x_0_3 x_3_4 x_3_5 x_4_6 x_5_6 x_6_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7464 (t x_0_3 x_0_5 x_1_2 x_2_3 x_3_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7465 (t x_0_8 x_2_3 x_3_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7467 (t x_1_3 x_2_3 x_2_5 x_3_4 x_3_5 x_5_6 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7468 (t x_0_4 x_1_4 x_4_5 x_4_7 x_4_9 : ℝ) : (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7470 (t x_0_3 x_2_3 x_3_5 x_3_6 x_5_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7473 (t x_1_4 x_1_7 x_4_5 x_5_6 x_5_7 x_6_8 x_7_10 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7474 (t x_0_5 x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7477 (t x_0_1 x_1_6 x_1_7 x_5_6 x_6_8 : ℝ) : ((t + ((-1) * x_1_7)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7478 (t x_0_6 x_2_6 x_6_7 x_6_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_2_6 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7479 (t x_0_1 x_1_2 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7481 (t x_0_1 x_1_3 x_1_8 x_3_5 x_5_6 x_5_8 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_5_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7482 (t x_0_6 x_1_6 x_4_6 x_6_7 x_6_8 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7483 (t x_0_3 x_3_4 x_3_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7485 (t x_1_5 x_4_8 x_5_8 x_8_10 x_8_9 : ℝ) : ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7487 (t x_0_3 x_2_3 x_3_4 x_3_5 x_5_6 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7488 (t x_0_3 x_3_4 x_3_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7489 (t x_0_5 x_0_6 x_1_3 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7490 (t x_0_1 x_0_2 x_1_4 x_2_4 x_4_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7491 (t x_0_3 x_3_4 x_3_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7493 (t x_0_3 x_2_3 x_3_4 x_3_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7495 (t x_0_3 x_2_3 x_3_4 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7496 (t x_1_2 x_2_3 x_2_6 x_3_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7499 (t x_0_3 x_1_3 x_2_3 x_3_5 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7500 (t x_0_5 x_0_6 x_2_3 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7502 (t x_0_6 x_3_6 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7503 (t x_0_4 x_4_6 x_6_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7504 (t x_0_3 x_1_2 x_2_3 x_2_8 x_3_4 x_3_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7506 (t x_0_6 x_1_3 x_2_6 x_3_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7508 (t x_0_6 x_2_6 x_6_7 x_6_8 x_7_8 x_8_10 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7510 (t x_0_2 x_2_4 x_4_7 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7511 (t x_0_3 x_0_6 x_1_3 x_3_4 x_3_6 x_6_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7513 (t x_0_5 x_1_2 x_2_5 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7514 (x_0_7 x_0_8 x_2_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7520 (t x_2_4 x_3_4 x_3_6 x_4_5 x_4_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7521 (t x_0_3 x_3_4 x_3_6 x_4_6 x_6_8 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7527 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7528 (t x_0_1 x_1_3 x_3_7 x_7_8 x_8_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7531 (t x_1_6 x_3_6 x_5_6 : ℝ) : (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) ∨ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7533 (t x_0_6 x_2_3 x_3_4 x_3_6 x_4_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7534 (t x_0_3 x_3_5 x_3_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7535 (t x_0_1 x_1_3 x_1_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7536 (t x_0_4 x_0_6 x_4_6 x_4_8 x_6_8 x_6_9 x_8_10 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7537 (t x_0_4 x_4_7 x_4_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7538 (t x_0_1 x_1_3 x_1_4 x_4_6 x_6_7 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7539 (t x_1_9 x_3_5 x_5_7 x_5_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_9 + ((-1) * x_5_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7541 (t x_4_5 x_4_6 x_5_6 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7542 (t x_0_5 x_1_5 x_4_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7543 (t x_0_1 x_1_4 x_3_4 x_4_7 x_4_8 : ℝ) : (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7545 (t x_3_4 x_3_6 x_4_6 : ℝ) : (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7546 (t x_3_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ (x_4_7 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7548 (t x_3_4 x_4_5 x_4_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7549 (t x_0_1 x_1_6 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7550 (t x_0_2 x_2_3 x_3_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7551 (t x_0_1 x_1_2 x_1_4 x_4_9 x_9_10 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7552 (t x_0_2 x_2_3 x_3_8 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7553 (t x_0_3 x_2_3 x_3_5 x_3_8 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7556 (t x_0_2 x_2_4 x_2_8 x_4_5 x_5_7 : ℝ) : (¬ (x_2_8 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7557 (t x_0_2 x_2_3 x_2_5 x_3_5 x_4_5 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7558 (t x_0_4 x_1_4 x_4_5 x_4_7 x_5_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7560 (x_1_5 x_1_6 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7562 (t x_0_5 x_3_5 x_3_6 x_5_6 x_5_7 x_5_8 x_6_10 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7563 (t x_0_2 x_2_3 x_3_6 x_6_8 x_8_10 : ℝ) : ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7564 (t x_0_1 x_1_2 x_1_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7565 (t x_0_3 x_2_3 x_2_6 x_3_4 x_3_6 x_6_10 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7568 (t x_0_5 x_2_3 x_3_4 x_3_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7569 (t x_0_1 x_1_2 x_1_7 x_1_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7574 (t x_0_5 x_1_2 x_2_4 x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7575 (t x_0_1 x_1_2 x_1_4 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7585 (t x_0_1 x_1_2 x_1_7 x_7_9 x_9_10 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7587 (t x_0_2 x_1_2 x_2_3 x_2_4 x_3_5 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7588 (t x_2_3 x_3_6 x_3_7 x_6_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7590 (t x_0_8 x_4_5 x_5_6 x_5_8 x_6_7 x_6_8 x_8_10 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7592 (t x_0_5 x_4_7 x_5_7 x_7_8 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7593 (t x_3_6 x_4_6 x_6_7 x_6_8 x_8_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7599 (t x_0_6 x_1_3 x_3_4 x_3_6 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7610 (t x_0_1 x_0_6 x_1_2 x_1_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7611 (t x_0_4 x_4_8 x_6_8 x_8_10 x_8_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7612 (t x_0_2 x_2_8 x_3_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7614 (t x_0_1 x_1_8 x_1_9 x_3_9 x_6_9 x_9_10 : ℝ) : (¬ (x_1_8 ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_3_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7616 (t x_0_5 x_0_6 x_4_6 x_4_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7617 (t x_0_4 x_0_5 x_4_5 x_5_6 x_5_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7618 (t x_0_5 x_3_5 x_5_6 x_5_7 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7622 (t x_0_1 x_1_6 x_2_6 x_6_10 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7623 (t x_0_2 x_1_2 x_2_4 x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7624 (t x_0_5 x_5_7 x_7_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7625 (t x_0_4 x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7629 (t x_0_4 x_4_5 x_5_7 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7630 (t x_0_1 x_0_6 x_0_8 x_1_2 x_2_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7631 (t x_2_6 x_3_6 x_4_5 x_5_6 x_6_10 x_6_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7635 (t x_3_6 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7636 (t x_0_5 x_5_8 x_7_8 : ℝ) : ((t + ((-1) * x_5_8) + x_7_8) ≥ 1) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7637 (t x_0_3 x_1_5 x_3_5 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7642 (t x_2_3 x_3_5 x_3_8 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_5_8 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7643 (t x_0_3 x_0_8 x_2_3 x_3_4 x_3_8 x_8_10 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7646 (t x_1_3 x_2_3 x_3_4 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7651 (t x_0_2 x_0_4 x_2_4 x_4_5 x_4_8 x_5_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7656 (t x_0_5 x_4_5 x_5_6 x_5_7 x_6_8 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7657 (t x_0_2 x_0_5 x_2_4 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7661 (t x_0_4 x_2_3 x_3_4 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7665 (t x_0_4 x_0_5 x_5_6 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7667 (t x_0_5 x_0_6 x_5_6 : ℝ) : (¬ (x_0_6 ≥ 0)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + x_0_6 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7668 (t x_1_6 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7677 (t x_1_5 x_4_5 x_5_6 x_5_9 x_6_8 x_8_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7679 (t x_0_1 x_1_5 x_4_5 x_5_6 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7684 (t x_0_4 x_1_3 x_2_4 x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7686 (t x_0_7 x_1_7 x_1_8 x_6_8 x_7_10 x_8_9 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ (x_0_7 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7689 (t x_3_5 x_5_6 x_5_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7691 (t x_0_4 x_2_4 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7694 (t x_0_4 x_2_3 x_3_4 x_4_8 x_8_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7696 (t x_0_1 x_1_3 x_1_7 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7697 (t x_0_1 x_1_7 x_3_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7698 (t x_0_2 x_2_5 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7700 (t x_0_2 x_2_4 x_4_7 x_6_7 x_7_9 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7701 (t x_0_1 x_1_4 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7702 (t x_1_2 x_2_3 x_2_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7703 (t x_0_1 x_1_6 x_4_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7704 (t x_1_2 x_2_3 x_2_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7706 (t x_0_3 x_1_2 x_2_3 x_3_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

end ElevenTheory
