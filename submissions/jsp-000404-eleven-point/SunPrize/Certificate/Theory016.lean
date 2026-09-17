import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory4364 (t x_0_3 x_1_3 x_3_4 x_3_9 x_4_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_4_9)) ≤ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4366 (t x_0_4 x_1_3 x_3_4 x_4_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_5_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4367 (t x_0_3 x_3_6 x_3_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4368 (t x_0_3 x_2_5 x_3_5 x_3_6 x_3_7 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4369 (t x_0_2 x_2_4 x_2_6 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1) ∨ (¬ (x_2_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4374 (t x_0_1 x_0_2 x_1_2 x_2_5 x_2_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4376 (t x_2_3 x_3_4 x_4_9 x_8_9 x_9_10 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4377 (t x_0_4 x_1_3 x_3_4 x_4_8 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4378 (t x_0_4 x_1_4 x_4_7 x_4_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4379 (t x_0_4 x_0_8 x_1_4 x_4_7 x_4_8 x_8_9 : ℝ) : ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ (x_1_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4380 (t x_0_5 x_2_5 x_5_6 x_5_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4385 (t x_0_4 x_1_3 x_3_4 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4388 (t x_0_4 x_0_8 x_1_3 x_3_4 x_4_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_4_9)) ≤ 0) ∨ (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4390 (t x_0_5 x_2_5 x_5_6 x_5_8 x_6_7 : ℝ) : ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4391 (t x_0_4 x_0_7 x_1_3 x_3_4 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≤ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4392 (t x_0_2 x_2_5 x_5_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4393 (x_0_1 x_0_9 x_1_6 x_1_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_1_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4394 (t x_0_1 x_1_5 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4396 (t x_3_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1) ∨ (¬ (x_3_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4402 (t x_0_6 x_1_3 x_3_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4403 (t x_0_4 x_1_3 x_3_4 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4404 (t x_0_6 x_1_3 x_3_6 x_6_9 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4406 (t x_0_3 x_1_3 x_3_4 x_3_7 x_7_9 : ℝ) : (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4407 (t x_0_7 x_1_2 x_2_6 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4410 (t x_0_3 x_1_6 x_3_5 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4413 (t x_0_3 x_0_6 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4414 (t x_0_3 x_1_3 x_3_5 x_3_6 x_3_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4415 (t x_0_7 x_1_3 x_3_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4416 (t x_0_5 x_1_3 x_3_5 x_5_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4419 (t x_0_5 x_1_3 x_3_5 x_5_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4420 (t x_0_1 x_0_3 x_3_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4421 (t x_0_5 x_1_3 x_3_5 x_5_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4423 (t x_5_7 x_6_9 x_7_8 x_7_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4425 (t x_0_3 x_3_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4428 (t x_0_5 x_1_3 x_3_5 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4429 (t x_4_5 x_5_6 x_5_8 x_6_8 x_8_10 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4430 (t x_0_3 x_3_4 x_4_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4431 (t x_0_5 x_0_7 x_1_3 x_3_5 x_5_7 x_7_10 x_7_8 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4432 (t x_5_10 x_5_7 x_7_10 : ℝ) : (((((x_5_7 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_5_7 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_5_7) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_7_10) ≥ 1))) ↔ ((¬ ((¬ ((x_5_10 + ((-1) * x_7_10)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((t + x_5_7 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + x_5_10 + ((-1) * x_7_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_5_10 + ((-1) * x_7_10)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_7) + x_5_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_10) + x_7_10) ≥ 1)))))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_7 + ((-1) * x_5_10)) ≥ 0) ↔ (((1) * x_5_10 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_5_7) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_7 + ((-1) * x_5_10)) ≤ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_5_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_5_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_5_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_5_7 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_5_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory4434 (t x_0_1 x_1_2 x_2_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4440 (t x_0_3 x_1_3 x_3_6 x_3_7 x_4_5 x_5_6 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4441 (t x_0_5 x_0_7 x_1_3 x_3_5 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4444 (t x_0_1 x_1_6 x_1_7 x_6_8 x_7_8 x_8_10 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4445 (t x_0_2 x_2_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4447 (t x_0_1 x_0_3 x_3_6 x_4_6 x_6_7 x_6_9 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4448 (t x_0_3 x_0_6 x_1_6 x_1_7 x_6_7 x_6_9 x_7_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4449 (t x_1_7 x_6_7 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4450 (t x_0_7 x_1_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_1_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4453 (t x_5_6 x_5_7 x_6_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4456 (t x_3_6 x_4_9 x_6_7 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_4_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4460 (t x_0_3 x_3_4 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4462 (t x_0_3 x_3_6 x_4_6 x_6_7 x_6_9 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_6_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4466 (t x_0_1 x_1_4 x_1_5 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4471 (x_0_1 x_0_3 x_1_5 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4476 (x_0_3 x_1_3 x_3_4 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4477 (t x_1_5 x_4_5 x_5_7 x_5_9 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4493 (t x_0_2 x_1_2 x_2_4 x_2_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4495 (x_0_9 x_3_10 x_3_9 x_9_10 : ℝ) : (¬ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_3_10)) ≥ 0)) ∨ (¬ ((x_3_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_3_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4496 (t x_4_10 x_4_8 x_8_10 : ℝ) : (((((x_4_8 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_4_8 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_4_8 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_4_8) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_8_10) ≥ 1))) ↔ ((¬ ((¬ ((x_4_10 + ((-1) * x_8_10)) ≤ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_4_8 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + x_4_10 + ((-1) * x_8_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_4_10 + ((-1) * x_8_10)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_8) + x_4_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_10) + x_8_10) ≥ 1)))))) := by
  classical
  have e0 : ((x_4_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_4_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_8 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_4_8 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_4_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_4_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_8 + ((-1) * x_4_10)) ≥ 0) ↔ (((1) * x_4_10 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_4_8) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_4_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory4498 (t x_2_5 x_4_5 x_5_6 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4499 (t x_0_1 x_1_3 x_3_4 x_4_5 x_5_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_5_9 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4503 (t x_0_3 x_3_4 x_4_6 x_4_8 x_6_8 x_8_9 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4506 (t x_2_5 x_4_8 x_5_6 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_4_8 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4507 (t x_1_5 x_4_5 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4509 (x_0_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4510 (x_0_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4511 (t x_0_3 x_1_3 x_1_7 x_3_5 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4513 (t x_4_6 x_6_7 x_6_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4514 (t x_0_3 x_3_4 x_3_9 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_3_9)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4517 (t x_0_4 x_0_6 x_1_3 x_3_4 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4519 (t x_1_3 x_3_4 x_3_5 x_4_6 x_6_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4522 (t x_3_6 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4523 (t x_1_3 x_3_6 x_4_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4525 (x_0_3 x_1_3 x_1_6 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4526 (t x_0_3 x_3_4 x_4_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4528 (t x_0_3 x_1_3 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4529 (t x_0_5 x_0_7 x_1_2 x_2_5 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_0_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4530 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_6 x_6_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4531 (t x_0_2 x_1_2 x_2_3 x_2_4 x_2_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_2_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4535 (t x_1_2 x_1_7 x_2_5 x_5_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4536 (t x_0_2 x_2_3 x_2_4 x_3_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4537 (t x_3_7 x_7_8 x_7_9 : ℝ) : (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1) ∨ ((t + ((-1) * x_7_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4538 (t x_0_3 x_1_3 x_3_4 x_3_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4539 (t x_0_7 x_1_3 x_3_5 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4540 (t x_0_8 x_1_3 x_3_5 x_3_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4541 (t x_0_5 x_2_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4543 (t x_1_2 x_2_5 x_5_9 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4546 (t x_0_5 x_1_2 x_2_5 x_5_7 x_7_9 x_9_10 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4547 (t x_2_3 x_3_4 x_4_6 x_6_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4548 (t x_0_6 x_1_3 x_3_5 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4549 (t x_0_1 x_1_2 x_2_6 x_4_6 x_6_7 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4550 (t x_0_1 x_1_4 x_2_4 x_4_10 x_4_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4551 (t x_2_10 x_2_4 x_4_10 : ℝ) : (((((x_2_4 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_4_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_4_10) ≥ 1))) ↔ ((¬ ((¬ ((x_2_10 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_10)) ≤ 0)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_10)) ≥ 1)) ∨ (¬ ((t + x_2_10 + ((-1) * x_4_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_10 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_10)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_10) + x_4_10) ≥ 1)))))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_10)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_10 + ((-1) * x_4_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_4 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_10 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_10 + ((-1) * x_4_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_2_4) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_2_10) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory4552 (t x_0_1 x_1_2 x_2_4 x_4_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4553 (t x_0_3 x_0_4 x_3_4 x_4_6 x_4_8 x_6_7 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4555 (t x_0_2 x_2_3 x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4557 (t x_0_5 x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4559 (t x_0_7 x_4_6 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4560 (t x_4_7 x_5_6 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4561 (t x_0_2 x_2_3 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4562 (t x_1_3 x_3_5 x_3_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4563 (t x_1_2 x_2_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4564 (x_0_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4565 (t x_4_5 x_5_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4570 (t x_0_5 x_1_2 x_2_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4571 (t x_0_5 x_1_3 x_3_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4572 (t x_0_5 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4574 (t x_0_5 x_2_3 x_3_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4575 (t x_0_3 x_2_3 x_3_4 x_3_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4576 (t x_0_3 x_3_4 x_3_5 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4577 (t x_0_7 x_3_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ (x_3_7 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4582 (t x_0_4 x_1_4 x_4_5 x_4_6 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4583 (t x_0_6 x_0_8 x_1_3 x_3_6 x_6_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4584 (t x_0_3 x_3_5 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ (x_5_9 ≥ 0)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4585 (t x_0_4 x_1_7 x_4_5 x_4_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_1_7 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4586 (t x_0_7 x_1_7 x_6_7 x_7_8 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4588 (t x_0_8 x_5_8 x_6_7 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4589 (t x_1_5 x_2_4 x_2_5 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4594 (t x_0_7 x_1_3 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4595 (t x_0_7 x_1_3 x_3_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4597 (t x_2_7 x_4_5 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4598 (t x_0_8 x_5_8 x_6_7 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4599 (t x_0_2 x_2_4 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4600 (t x_0_6 x_1_3 x_3_6 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4602 (x_0_4 x_0_6 x_0_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_0_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4603 (t x_0_1 x_1_2 x_2_4 x_4_8 x_8_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4604 (t x_0_6 x_0_7 x_4_6 x_5_7 x_6_9 x_7_8 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4606 (t x_0_5 x_1_3 x_3_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4608 (t x_0_5 x_1_3 x_3_5 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4610 (t x_0_4 x_1_3 x_3_4 x_4_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4611 (t x_0_2 x_1_6 x_2_3 x_2_6 x_6_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_6 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4612 (t x_0_2 x_1_2 x_2_6 x_2_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4614 (t x_0_3 x_1_4 x_3_4 x_4_6 x_4_8 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4615 (t x_1_3 x_3_5 x_3_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_3_5 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4617 (t x_0_2 x_2_5 x_2_6 x_4_5 x_5_8 : ℝ) : ((t + ((-1) * x_2_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4618 (t x_2_3 x_3_5 x_3_7 x_5_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4619 (t x_4_6 x_5_7 x_6_7 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4620 (t x_3_5 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4621 (t x_0_5 x_1_2 x_2_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4622 (t x_0_5 x_4_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4623 (t x_0_5 x_5_6 x_5_8 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4626 (t x_0_5 x_0_6 x_1_3 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4628 (t x_0_2 x_0_7 x_1_2 x_2_5 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4629 (t x_1_2 x_2_5 x_2_6 x_5_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4630 (t x_0_5 x_1_2 x_2_5 x_5_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4636 (t x_4_5 x_5_6 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4639 (t x_1_2 x_2_4 x_2_5 x_4_5 x_5_9 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4642 (t x_0_6 x_1_2 x_2_6 x_6_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4643 (t x_0_3 x_1_3 x_3_4 x_3_7 x_4_6 x_6_7 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4644 (t x_1_10 x_1_8 x_8_10 : ℝ) : (((((x_1_8 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_1_8 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_1_8 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_8_10) ≥ 1))) ↔ ((¬ ((¬ ((x_1_10 + ((-1) * x_8_10)) ≤ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((t + x_1_8 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((t + x_1_10 + ((-1) * x_8_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_10 + ((-1) * x_8_10)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_8) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_8_10) ≥ 1)))))) := by
  classical
  have e0 : ((x_1_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_1_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_8 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_1_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_8 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_1_8) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_1_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory4646 (t x_0_6 x_1_3 x_3_6 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4647 (t x_0_6 x_1_3 x_3_6 x_6_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4648 (t x_2_3 x_3_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4649 (t x_0_7 x_1_3 x_3_6 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_3_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4654 (t x_0_1 x_1_5 x_2_5 x_5_7 x_5_8 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4655 (t x_0_1 x_1_5 x_2_3 x_2_5 x_3_4 x_5_7 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4656 (t x_3_4 x_4_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4657 (t x_0_1 x_0_3 x_1_3 x_3_5 x_3_7 x_5_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4660 (t x_0_4 x_2_4 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4663 (x_0_1 x_1_3 x_1_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4664 (t x_0_1 x_1_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4665 (t x_1_2 x_2_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4666 (t x_0_1 x_1_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4667 (t x_0_1 x_1_4 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4668 (t x_0_1 x_1_4 x_1_5 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ (x_1_4 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4669 (t x_0_3 x_3_4 x_3_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4670 (t x_0_2 x_1_3 x_2_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4672 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_7 : ℝ) : (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4673 (t x_0_3 x_1_3 x_3_5 x_3_7 x_5_6 x_7_8 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4674 (t x_0_2 x_2_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4675 (t x_0_1 x_1_2 x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_2_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4677 (t x_0_1 x_1_5 x_5_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4679 (x_1_3 x_1_4 x_1_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ ((x_1_4 + ((-1) * x_1_5)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory4680 (t x_0_4 x_0_5 x_1_2 x_2_4 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4683 (t x_1_2 x_2_5 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4684 (t x_4_5 x_5_6 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4685 (t x_0_1 x_1_2 x_2_3 x_3_7 x_7_8 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4686 (t x_0_1 x_1_2 x_1_3 x_2_3 x_3_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4687 (t x_0_1 x_1_2 x_1_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4688 (t x_0_1 x_1_2 x_2_7 x_2_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_2_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4689 (t x_0_1 x_1_2 x_2_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4691 (t x_0_1 x_1_2 x_2_8 x_7_8 x_8_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4692 (t x_0_3 x_3_6 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4694 (t x_0_3 x_3_6 x_3_7 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4698 (t x_0_5 x_3_4 x_3_5 x_5_8 : ℝ) : ((t + ((-1) * x_3_4) + x_3_5) ≥ 1) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory4700 (t x_1_3 x_2_3 x_3_6 x_3_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4701 (t x_0_1 x_1_2 x_1_4 x_4_5 x_5_9 : ℝ) : (¬ (x_5_9 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4702 (t x_0_1 x_0_3 x_1_3 x_3_4 x_3_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4704 (t x_0_4 x_3_6 x_4_6 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_3_6 ≥ 0)) ∨ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory4705 (t x_0_1 x_1_3 x_3_4 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4706 (t x_1_4 x_4_6 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4707 (t x_0_6 x_1_4 x_3_4 x_4_5 x_4_6 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory4710 (t x_1_5 x_2_4 x_2_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ (x_2_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory4711 (t x_4_5 x_5_6 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4713 (t x_0_1 x_1_4 x_3_4 x_4_5 x_4_6 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4715 (t x_1_5 x_5_6 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4716 (t x_0_1 x_1_3 x_3_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4717 (t x_0_1 x_1_3 x_3_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4718 (t x_0_1 x_1_3 x_3_4 x_4_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory4721 (t x_0_1 x_1_6 x_3_4 x_3_6 x_4_5 x_6_8 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

end ElevenTheory
