import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory6212 (t x_0_4 x_0_6 x_2_3 x_3_4 x_4_6 x_6_7 x_6_9 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6213 (t x_3_9 x_4_6 x_6_7 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_3_9 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6214 (t x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6216 (x_0_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6217 (t x_0_5 x_4_5 x_5_6 x_5_7 x_7_9 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6218 (x_0_5 x_3_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6221 (x_0_1 x_1_3 x_1_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6224 (t x_0_5 x_1_3 x_3_4 x_3_5 x_4_5 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6225 (t x_0_5 x_1_2 x_2_4 x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6226 (t x_0_2 x_0_5 x_1_2 x_2_4 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6229 (t x_3_5 x_4_5 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6230 (t x_0_2 x_1_2 x_2_4 x_2_6 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6231 (t x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6233 (t x_0_4 x_1_2 x_2_4 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6234 (t x_0_2 x_1_2 x_2_4 x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6235 (t x_1_2 x_2_6 x_5_6 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6238 (t x_1_2 x_2_5 x_5_6 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6239 (x_1_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6240 (t x_3_4 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : ((t + ((-1) * x_5_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6241 (t x_0_3 x_1_3 x_3_4 x_3_6 x_4_5 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6243 (t x_2_3 x_3_4 x_3_6 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6244 (t x_0_4 x_1_2 x_2_4 x_4_7 x_5_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6245 (t x_0_3 x_2_3 x_3_6 x_3_7 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6246 (x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6247 (t x_3_7 x_4_7 x_5_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6248 (t x_3_8 x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6250 (t x_0_2 x_2_5 x_3_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6251 (t x_0_1 x_1_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6252 (t x_0_1 x_1_4 x_1_6 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_6)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6254 (t x_1_4 x_2_4 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6255 (t x_0_3 x_2_3 x_3_4 x_3_8 x_4_6 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6256 (t x_1_4 x_3_4 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6257 (t x_0_3 x_2_3 x_2_4 x_3_4 x_3_5 x_4_6 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6259 (t x_0_3 x_1_3 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6260 (t x_0_1 x_1_5 x_1_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6262 (t x_0_4 x_2_4 x_4_6 x_4_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6263 (t x_0_7 x_2_3 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6264 (t x_2_5 x_4_5 x_5_7 x_5_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6266 (t x_0_1 x_1_4 x_4_5 x_5_8 x_8_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6267 (t x_0_2 x_2_8 x_7_8 x_8_10 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6271 (t x_0_4 x_4_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6274 (t x_0_2 x_2_3 x_3_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6275 (t x_0_2 x_2_5 x_5_7 x_7_9 x_9_10 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6276 (t x_0_3 x_0_7 x_3_5 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6277 (t x_0_3 x_2_3 x_3_4 x_3_6 x_4_6 x_6_7 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6281 (t x_0_4 x_3_4 x_4_6 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6282 (t x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6284 (t x_0_4 x_3_4 x_4_5 x_4_8 x_5_6 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6286 (t x_0_1 x_1_2 x_1_6 x_2_3 x_2_6 x_3_4 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ (x_3_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6287 (t x_0_1 x_1_3 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6288 (t x_0_3 x_1_3 x_1_5 x_3_4 x_3_5 x_3_6 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6289 (t x_3_4 x_4_6 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6291 (t x_6_7 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6292 (t x_0_2 x_2_4 x_4_5 x_4_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6295 (t x_0_3 x_0_4 x_3_5 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6296 (t x_1_4 x_2_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6298 (t x_0_3 x_0_4 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6299 (t x_4_5 x_5_7 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6300 (t x_0_3 x_3_4 x_4_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6303 (t x_0_4 x_0_5 x_1_4 x_4_5 x_4_6 x_5_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6304 (t x_2_3 x_3_6 x_3_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6305 (t x_0_2 x_2_3 x_3_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6309 (t x_0_4 x_1_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6314 (t x_0_1 x_1_5 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6315 (t x_0_2 x_2_7 x_6_7 x_7_10 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6316 (t x_0_1 x_1_4 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6317 (t x_0_1 x_1_3 x_1_4 x_3_4 x_4_6 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6318 (t x_0_1 x_1_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6321 (t x_0_2 x_2_3 x_3_8 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6323 (t x_1_2 x_2_3 x_2_4 x_3_4 x_4_6 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6324 (t x_0_3 x_0_5 x_1_2 x_2_3 x_3_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6325 (t x_0_1 x_1_2 x_1_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6326 (t x_0_4 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6328 (t x_0_1 x_1_3 x_1_5 x_3_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6332 (t x_0_3 x_1_2 x_2_3 x_3_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6333 (t x_0_6 x_3_7 x_6_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6334 (t x_0_3 x_3_6 x_6_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6335 (t x_0_2 x_1_2 x_2_4 x_2_5 x_4_6 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6336 (t x_0_1 x_1_2 x_1_4 x_2_4 x_4_6 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6339 (t x_0_4 x_3_4 x_4_5 x_4_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6341 (t x_0_4 x_3_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6342 (t x_0_4 x_1_2 x_1_4 x_2_3 x_3_4 x_4_5 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6344 (t x_0_4 x_1_5 x_3_4 x_4_5 x_4_8 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_5_8)) ≤ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6345 (t x_6_10 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + x_6_9 + ((-1) * x_6_10)) ≥ 1) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_6_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6348 (t x_1_2 x_2_3 x_2_7 x_3_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6350 (t x_0_4 x_1_4 x_4_5 x_4_6 x_4_7 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6352 (t x_3_4 x_4_5 x_4_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6356 (t x_0_4 x_1_3 x_3_4 x_4_6 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6357 (t x_0_5 x_5_6 x_5_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6358 (t x_0_3 x_3_7 x_3_8 x_7_8 x_8_10 x_8_9 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6360 (x_0_5 x_0_8 x_3_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6363 (t x_0_1 x_1_3 x_1_6 x_3_6 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6364 (x_0_3 x_1_3 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6369 (t x_1_4 x_3_4 x_4_6 x_4_8 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6370 (t x_0_1 x_1_4 x_2_4 x_4_6 x_4_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6371 (t x_1_2 x_2_3 x_2_6 x_3_6 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6372 (t x_0_3 x_1_2 x_2_3 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6373 (t x_0_1 x_1_2 x_1_4 x_4_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6376 (t x_0_4 x_1_4 x_4_6 x_4_8 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6378 (t x_0_4 x_1_4 x_4_6 x_4_7 x_7_9 : ℝ) : (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6381 (t x_0_2 x_2_3 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6384 (t x_0_3 x_0_4 x_0_8 x_3_4 x_3_8 x_4_5 x_8_9 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6385 (t x_0_2 x_2_3 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6388 (t x_0_3 x_3_4 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6391 (t x_0_1 x_1_2 x_2_4 x_4_7 x_7_8 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6393 (t x_0_1 x_1_2 x_1_7 x_2_4 x_2_7 x_7_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_7)) ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6395 (t x_0_1 x_1_4 x_4_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6397 (t x_0_5 x_1_2 x_2_5 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6399 (t x_0_8 x_1_4 x_4_8 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1) ∨ (¬ (x_0_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6406 (t x_0_3 x_0_7 x_3_5 x_3_7 x_3_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((t + x_3_5 + ((-1) * x_3_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6410 (t x_1_7 x_6_10 x_6_7 x_7_10 : ℝ) : ((t + ((-1) * x_6_10)) ≤ 0) ∨ (¬ (x_1_7 ≥ 0)) ∨ ((t + x_6_7 + ((-1) * x_6_10)) ≥ 1) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory6411 (t x_0_1 x_0_2 x_1_2 x_2_5 x_2_7 x_5_7 x_7_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6413 (t x_1_6 x_3_4 x_4_6 x_4_7 x_6_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_6)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6414 (t x_0_7 x_3_4 x_4_7 x_5_8 x_7_8 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6415 (t x_0_2 x_2_3 x_2_4 x_4_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6416 (t x_0_1 x_1_5 x_5_9 x_8_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6417 (t x_0_7 x_6_7 x_7_10 x_7_8 x_8_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_7 ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6418 (x_0_5 x_1_5 x_2_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_2_5)) ≥ 0) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6419 (x_1_6 x_2_10 x_2_6 x_6_10 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_2_10 + ((-1) * x_6_10)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_2_10)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6420 (t x_0_6 x_1_2 x_2_3 x_2_6 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6421 (t x_0_1 x_1_2 x_1_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6424 (t x_1_5 x_3_7 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6426 (t x_0_4 x_2_4 x_4_6 x_4_8 x_8_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6427 (t x_0_3 x_1_7 x_3_7 x_6_7 x_7_10 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6430 (t x_1_4 x_4_7 x_6_7 x_7_10 x_7_8 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6435 (t x_0_5 x_3_5 x_3_7 x_4_6 x_4_7 x_5_9 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≥ 0)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6439 (t x_0_4 x_0_8 x_2_3 x_3_5 x_3_8 x_8_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6442 (t x_0_1 x_1_5 x_1_6 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6444 (t x_1_5 x_4_5 x_5_6 x_5_8 x_6_8 x_8_10 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6445 (t x_0_1 x_0_3 x_1_3 x_1_5 x_1_6 x_3_4 x_3_7 x_4_7 x_5_6 x_6_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_5) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory6448 (t x_0_6 x_1_6 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ (x_0_6 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6449 (t x_0_4 x_4_5 x_4_7 x_5_7 x_7_10 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6450 (t x_0_1 x_0_2 x_1_2 x_2_5 x_2_7 x_5_7 x_7_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_10)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6453 (t x_0_1 x_1_5 x_2_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6457 (t x_0_1 x_1_2 x_1_5 x_2_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6460 (t x_1_3 x_3_5 x_3_8 x_5_8 x_8_10 x_8_9 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6461 (t x_0_5 x_1_2 x_1_3 x_3_5 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6463 (t x_0_1 x_1_6 x_2_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6465 (t x_0_4 x_1_2 x_2_3 x_2_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6466 (t x_0_1 x_1_2 x_1_4 x_4_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6468 (t x_0_3 x_2_3 x_3_4 x_3_9 x_4_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6469 (t x_0_2 x_0_4 x_2_4 x_4_6 x_4_8 x_6_7 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6472 (t x_0_3 x_1_3 x_2_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6473 (t x_0_3 x_1_2 x_2_3 x_3_5 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6476 (t x_2_3 x_3_7 x_3_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6477 (t x_2_3 x_3_5 x_4_9 x_5_9 x_9_10 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6480 (t x_1_5 x_2_3 x_2_4 x_4_5 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6483 (t x_0_1 x_1_2 x_1_8 x_8_9 x_9_10 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6485 (t x_0_4 x_1_4 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6486 (t x_0_4 x_0_8 x_1_4 x_4_6 x_4_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_4_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6487 (x_3_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6488 (t x_0_2 x_1_2 x_2_3 x_2_5 x_3_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6490 (t x_0_3 x_0_4 x_3_4 x_4_5 x_4_8 x_5_7 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6493 (t x_0_4 x_3_4 x_4_6 x_4_9 x_6_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_4 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6494 (t x_0_4 x_3_4 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6495 (t x_0_1 x_1_3 x_1_9 x_3_4 x_4_7 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6497 (t x_0_4 x_2_3 x_3_4 x_3_8 x_4_8 : ℝ) : (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory6499 (t x_0_5 x_0_7 x_4_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6500 (t x_1_4 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6501 (t x_0_1 x_1_5 x_2_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6502 (t x_0_1 x_1_2 x_1_5 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6503 (t x_1_5 x_1_7 x_3_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6505 (t x_0_4 x_4_6 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6509 (t x_0_2 x_0_3 x_3_4 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6511 (t x_0_2 x_0_3 x_3_4 x_3_5 x_4_5 x_5_10 x_5_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_10)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6512 (t x_0_2 x_2_4 x_4_5 x_5_6 x_6_10 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_10)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6516 (t x_0_1 x_1_2 x_1_6 x_3_6 x_6_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6517 (t x_0_2 x_2_3 x_3_7 x_5_6 x_5_7 x_7_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6520 (t x_2_4 x_4_6 x_4_9 x_8_9 x_9_10 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6521 (t x_3_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6524 (t x_0_4 x_1_4 x_1_5 x_4_5 x_4_7 x_5_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6528 (t x_1_5 x_3_5 x_5_7 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ (x_1_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6530 (t x_1_4 x_3_4 x_4_5 x_4_7 x_5_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6534 (t x_0_2 x_2_3 x_3_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6536 (t x_0_2 x_2_4 x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6537 (t x_0_5 x_2_5 x_4_6 x_5_6 x_5_8 x_6_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6540 (t x_0_2 x_2_3 x_3_4 x_4_6 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6542 (t x_0_4 x_1_4 x_1_6 x_4_6 : ℝ) : (¬ (x_1_6 ≥ 0)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory6543 (t x_4_7 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6544 (t x_3_6 x_4_7 x_6_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6545 (t x_0_2 x_1_2 x_2_4 x_2_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6546 (t x_0_2 x_2_4 x_2_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_2_4 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6548 (t x_1_3 x_1_5 x_2_3 x_3_5 x_3_6 x_5_8 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6549 (t x_0_3 x_2_3 x_3_6 x_3_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6550 (t x_0_4 x_1_2 x_2_4 x_4_8 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6554 (t x_0_2 x_0_3 x_2_4 x_3_4 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory6555 (x_0_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6556 (t x_0_4 x_2_4 x_4_6 x_4_7 x_6_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_2_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6557 (t x_0_2 x_1_2 x_1_7 x_2_3 x_3_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_3_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6559 (t x_0_2 x_2_5 x_3_5 x_5_6 x_5_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6560 (t x_0_4 x_3_4 x_4_5 x_4_6 x_5_7 : ℝ) : (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6561 (t x_0_2 x_1_2 x_2_3 x_2_7 x_7_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6562 (t x_0_2 x_2_3 x_2_7 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_2_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_2_3) + x_2_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6564 (t x_0_6 x_1_4 x_4_6 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6565 (t x_0_4 x_4_5 x_4_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6566 (t x_0_1 x_1_2 x_2_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6567 (t x_0_1 x_1_2 x_1_3 x_2_6 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6568 (t x_0_2 x_1_5 x_2_5 x_5_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6571 (t x_0_3 x_1_3 x_3_4 x_3_6 x_3_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_3_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6573 (t x_0_2 x_1_2 x_2_3 x_2_5 x_2_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

end ElevenTheory
