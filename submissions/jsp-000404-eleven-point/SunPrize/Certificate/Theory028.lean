import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory8862 (t x_0_2 x_0_4 x_2_3 x_3_6 x_4_7 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory8864 (t x_0_3 x_3_6 x_6_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8865 (t x_0_1 x_1_3 x_1_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8866 (t x_0_1 x_1_3 x_1_8 x_8_9 x_9_10 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8869 (t x_0_7 x_1_7 x_2_8 x_7_8 x_7_9 x_8_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ (x_2_8 ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8870 (t x_0_5 x_2_5 x_2_8 x_5_8 x_5_9 x_8_10 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_2_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8876 (t x_2_4 x_3_4 x_4_5 x_4_9 x_5_6 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8879 (t x_0_2 x_0_3 x_0_4 x_2_4 x_2_7 x_3_6 x_4_7 x_4_9 x_6_9 x_7_10 x_9_10 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_4_9 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory8880 (t x_0_1 x_0_2 x_0_4 x_1_2 x_1_6 x_1_9 x_4_7 x_5_7 x_7_10 x_7_8 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_6) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory8884 (t x_0_4 x_4_5 x_5_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8885 (t x_0_1 x_1_7 x_5_7 x_7_10 x_7_8 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8886 (t x_0_6 x_3_6 x_4_6 x_6_7 x_6_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8889 (t x_0_4 x_3_4 x_4_6 x_4_9 x_9_10 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8891 (t x_0_1 x_1_5 x_1_7 x_5_7 x_7_10 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8892 (t x_0_7 x_1_7 x_1_8 x_5_8 x_7_10 x_8_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_0_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8894 (t x_0_1 x_0_8 x_1_5 x_2_4 x_4_5 x_4_8 x_5_7 x_7_8 x_8_9 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory8895 (t x_0_4 x_2_4 x_4_6 x_4_8 x_6_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8896 (t x_0_8 x_1_2 x_2_4 x_2_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_8 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8898 (t x_0_3 x_1_3 x_3_7 x_3_9 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8899 (t x_4_5 x_5_6 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8901 (t x_2_4 x_4_6 x_4_8 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8902 (t x_2_4 x_4_5 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8903 (t x_4_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8904 (t x_0_7 x_1_7 x_2_3 x_3_5 x_3_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8907 (t x_0_8 x_1_3 x_3_7 x_3_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8909 (t x_0_4 x_1_3 x_2_4 x_3_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8912 (t x_0_2 x_2_4 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8914 (t x_0_3 x_2_5 x_3_5 : ℝ) : ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_2_5) + x_3_5) ≥ 1) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8915 (t x_0_6 x_3_4 x_4_6 x_6_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8916 (t x_0_1 x_1_3 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8918 (t x_3_6 x_3_7 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_3_7 ≥ 0)) ∨ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8919 (t x_0_9 x_1_9 x_2_4 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_5_9)) ≤ 0) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_1_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8921 (x_0_6 x_2_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8922 (t x_0_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8923 (t x_0_5 x_1_5 x_4_5 x_5_7 x_5_8 x_8_9 : ℝ) : ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8924 (x_1_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ ((x_1_3 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8925 (t x_0_4 x_2_4 x_4_5 x_4_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8927 (t x_0_4 x_1_3 x_3_4 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8928 (t x_3_6 x_3_8 x_4_6 x_5_8 x_6_10 x_8_9 : ℝ) : ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8929 (t x_2_4 x_3_4 x_3_8 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_8)) ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8930 (t x_2_5 x_4_5 x_5_7 x_5_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8933 (t x_0_8 x_2_4 x_4_5 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8936 (t x_0_2 x_0_4 x_4_5 x_4_6 x_5_6 x_6_10 x_6_9 : ℝ) : (¬ (x_6_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8937 (t x_0_4 x_1_3 x_2_4 x_3_4 x_4_5 x_4_6 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8939 (t x_0_3 x_1_4 x_2_3 x_2_4 x_2_7 x_3_4 x_4_6 x_4_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory8943 (t x_0_1 x_1_3 x_3_7 x_7_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8945 (t x_0_1 x_1_4 x_1_5 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8946 (t x_0_1 x_1_2 x_1_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8947 (t x_0_4 x_1_4 x_4_5 x_4_7 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8948 (t x_0_1 x_1_4 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8949 (t x_0_3 x_2_3 x_3_5 x_3_8 x_5_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8950 (t x_0_5 x_3_5 x_5_7 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8951 (t x_0_1 x_1_4 x_1_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8954 (t x_0_2 x_0_3 x_0_4 x_2_4 x_2_6 x_3_5 x_4_5 x_4_6 x_5_8 x_6_9 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory8955 (t x_0_4 x_2_4 x_4_6 x_4_8 x_4_9 : ℝ) : ((t + ((-1) * x_4_9)) ≤ 0) ∨ (¬ (x_4_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8956 (t x_0_1 x_1_2 x_1_8 x_2_4 x_4_5 x_4_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8958 (t x_2_6 x_3_7 x_6_7 x_6_8 x_7_10 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_10)) ≥ 1)) ∨ ((t + ((-1) * x_3_7)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8960 (t x_0_7 x_0_8 x_3_5 x_5_6 x_5_8 x_8_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_0_7 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8962 (t x_0_1 x_1_6 x_1_7 x_4_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8963 (t x_0_5 x_3_5 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8964 (t x_2_3 x_3_4 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8965 (t x_1_4 x_1_7 x_4_7 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_1_7 ≥ 0)) ∨ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8967 (t x_2_3 x_3_4 x_3_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8971 (t x_0_2 x_0_3 x_2_3 x_3_5 x_3_9 x_5_9 x_9_10 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8972 (t x_0_2 x_2_8 x_5_8 x_8_10 x_8_9 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8973 (x_4_6 x_4_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≥ 0)) ∨ ((x_4_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8974 (t x_1_4 x_3_6 x_4_6 x_4_7 x_6_9 : ℝ) : ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8975 (t x_0_1 x_1_2 x_1_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8977 (t x_1_2 x_2_3 x_2_8 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8978 (t x_0_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8982 (t x_0_5 x_3_5 x_5_6 x_5_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8984 (x_4_7 x_4_8 x_4_9 : ℝ) : ((x_4_7 + ((-1) * x_4_9)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8986 (t x_0_1 x_1_2 x_1_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8987 (t x_0_1 x_1_2 x_1_8 x_2_4 x_4_6 x_4_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8988 (t x_0_1 x_1_2 x_1_6 x_2_4 x_4_6 x_4_7 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8989 (t x_0_4 x_2_4 x_4_6 x_4_9 x_6_7 : ℝ) : (¬ (x_2_4 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8993 (t x_0_4 x_2_5 x_4_5 x_5_7 x_5_8 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8996 (t x_3_6 x_5_6 x_6_7 x_6_9 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8998 (t x_0_5 x_3_5 x_5_6 x_5_9 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9000 (t x_0_3 x_3_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9001 (t x_3_5 x_4_8 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_4_8 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ ((t + x_4_8 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9002 (t x_0_6 x_3_5 x_5_6 x_5_7 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_6 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9003 (x_3_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9004 (x_2_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9005 (t x_3_6 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9008 (x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9009 (x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9010 (t x_0_1 x_0_3 x_1_3 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9011 (t x_0_4 x_1_3 x_2_3 x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9014 (x_0_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9015 (t x_0_3 x_0_4 x_3_4 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4) + x_3_4) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9016 (x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9018 (x_1_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9020 (t x_0_6 x_0_7 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_7)) ≤ 0) ∨ (¬ (x_0_6 ≥ 0)) ∨ ((t + ((-1) * x_0_7) + x_6_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9021 (x_0_2 x_2_5 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_2_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9022 (t x_0_2 x_2_5 x_2_8 x_3_5 x_5_8 : ℝ) : (¬ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_5_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9023 (x_0_1 x_1_2 x_1_3 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9024 (x_0_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9025 (x_1_2 x_2_6 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9027 (t x_0_1 x_1_2 x_1_4 x_2_4 x_2_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9030 (x_0_2 x_2_7 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_2_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9031 (x_0_2 x_0_7 x_2_8 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_7_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9032 (x_1_2 x_2_6 x_2_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9034 (t x_0_7 x_1_6 x_1_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9036 (x_5_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9037 (x_5_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9041 (x_0_4 x_2_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9042 (x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9045 (x_2_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9046 (x_2_4 x_2_6 x_4_7 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9049 (x_1_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9050 (t x_0_2 x_0_7 x_1_7 x_2_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9052 (t x_1_2 x_2_5 x_2_7 x_4_5 x_5_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9054 (t x_0_2 x_2_3 x_2_5 x_3_4 x_3_5 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9055 (t x_0_3 x_1_2 x_2_3 x_2_4 x_3_4 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9056 (x_1_2 x_2_4 x_2_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9062 (x_0_4 x_1_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9063 (x_3_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9064 (x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9065 (t x_0_4 x_2_4 x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9068 (t x_0_1 x_0_3 x_1_3 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9069 (x_2_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9072 (t x_0_7 x_1_2 x_1_7 x_2_3 x_2_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9074 (t x_0_3 x_0_5 x_3_5 x_3_7 x_5_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_3_5 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9076 (x_0_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9080 (x_1_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9081 (x_0_4 x_1_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9084 (t x_1_2 x_1_3 x_2_3 x_2_7 x_3_4 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9086 (x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9087 (t x_1_3 x_2_3 x_2_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9088 (x_2_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9090 (x_0_2 x_2_3 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9091 (x_0_6 x_1_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9092 (x_2_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9094 (x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9095 (x_0_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9096 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1) ∨ (¬ (x_0_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9097 (x_0_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9098 (x_0_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9099 (x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9100 (x_0_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9101 (t x_0_4 x_1_2 x_1_4 x_2_3 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9103 (t x_5_7 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_5_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9104 (x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9105 (x_0_3 x_3_5 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9106 (x_0_3 x_0_5 x_3_7 x_5_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9107 (t x_0_4 x_3_7 x_4_7 x_4_9 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_3_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9108 (x_0_4 x_4_7 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9111 (x_1_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9112 (t x_1_5 x_5_7 x_5_9 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9113 (x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9114 (x_1_3 x_3_8 x_3_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_3_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9117 (x_1_2 x_2_4 x_2_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9119 (x_1_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_5_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9120 (t x_1_5 x_1_9 x_2_5 x_5_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_1_5) + x_2_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9122 (x_0_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9123 (x_3_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9124 (x_0_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9125 (x_2_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9126 (x_0_7 x_1_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9127 (x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9129 (x_0_2 x_2_4 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9130 (t x_0_1 x_0_4 x_1_2 x_2_3 x_3_8 x_4_5 x_5_6 x_6_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_3_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory9131 (t x_0_3 x_0_7 x_3_5 x_5_6 x_6_10 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((t + x_0_3 + ((-1) * x_0_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_6_10 + ((-1) * x_9_10)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory9132 (t x_0_3 x_0_7 x_3_5 x_5_6 x_6_10 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((t + x_0_3 + ((-1) * x_0_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory9136 (x_0_3 x_3_4 x_3_6 x_3_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9137 (x_0_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9138 (t x_6_8 x_6_9 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9139 (x_3_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9140 (x_1_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9141 (t x_0_4 x_1_8 x_4_8 x_4_9 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9144 (x_4_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9145 (x_1_5 x_2_5 x_5_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9146 (t x_1_2 x_1_5 x_2_4 x_2_5 x_5_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_5) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9147 (x_0_4 x_3_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9148 (x_2_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9154 (x_0_6 x_1_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9160 (t x_0_5 x_1_5 x_2_4 x_4_5 x_4_6 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9161 (x_2_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9162 (t x_0_1 x_1_4 x_1_5 x_3_4 x_4_7 : ℝ) : ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory9165 (t x_0_1 x_0_3 x_1_3 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_1_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9167 (x_2_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9178 (x_1_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9180 (x_0_2 x_1_2 x_2_4 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory9183 (x_1_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9184 (x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9185 (x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9186 (x_0_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9189 (x_4_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9191 (t x_0_6 x_1_6 x_5_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory9193 (x_1_2 x_2_3 x_2_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9194 (x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9195 (x_2_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9196 (x_1_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9197 (x_0_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9198 (x_0_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9199 (x_2_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9200 (x_1_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9201 (x_1_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory9203 (x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

end ElevenTheory
