import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory6969 (x_4_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory6970 (t x_0_5 x_1_5 x_5_6 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6971 (x_0_2 x_0_7 x_2_5 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6973 (t x_0_6 x_3_4 x_4_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6974 (t x_0_1 x_1_2 x_2_3 x_3_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ (x_4_8 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6977 (t x_0_2 x_2_3 x_3_4 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6978 (t x_0_2 x_2_6 x_3_5 x_3_6 x_5_7 x_6_10 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6980 (t x_1_2 x_2_3 x_3_8 x_8_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6981 (t x_3_9 x_4_5 x_5_6 x_5_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_3_9 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6982 (t x_0_2 x_0_3 x_2_3 x_3_6 x_3_9 x_6_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6986 (t x_0_1 x_1_3 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6987 (t x_0_5 x_1_2 x_2_5 x_5_7 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6990 (t x_0_4 x_1_2 x_2_4 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6992 (t x_1_5 x_3_5 x_5_6 x_5_7 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory6993 (t x_0_4 x_1_2 x_2_4 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6994 (t x_0_6 x_1_2 x_2_6 x_6_7 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6996 (t x_0_1 x_1_3 x_2_3 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory6997 (t x_0_4 x_3_4 x_4_5 x_4_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory6998 (t x_0_4 x_1_2 x_2_4 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7001 (t x_0_1 x_1_3 x_3_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7002 (t x_1_3 x_2_3 x_3_6 x_3_8 x_6_7 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7003 (t x_0_6 x_1_4 x_4_6 x_5_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7004 (t x_0_3 x_1_3 x_1_8 x_3_7 x_3_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_7)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7005 (t x_0_4 x_1_3 x_3_5 x_3_7 x_4_6 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7006 (t x_0_4 x_0_6 x_3_4 x_4_5 x_4_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7007 (t x_0_5 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7011 (t x_0_5 x_0_6 x_1_4 x_4_5 x_5_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7012 (t x_1_3 x_3_5 x_3_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7021 (t x_0_2 x_0_4 x_2_4 : ℝ) : ((t + ((-1) * x_0_4) + x_2_4) ≥ 1) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7024 (t x_0_6 x_2_3 x_3_6 x_6_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7025 (t x_0_3 x_2_4 x_3_4 x_3_6 x_4_6 x_4_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7027 (t x_2_5 x_3_4 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7028 (t x_1_4 x_2_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7029 (t x_0_2 x_1_4 x_2_3 x_2_4 x_4_5 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7033 (t x_0_1 x_1_3 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7034 (t x_0_3 x_0_4 x_1_2 x_2_4 x_3_7 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7035 (t x_0_5 x_0_6 x_4_5 x_5_6 x_5_7 x_6_8 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7037 (t x_0_7 x_1_3 x_3_4 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_7 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7038 (t x_0_4 x_0_7 x_1_2 x_2_4 x_7_9 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7040 (t x_1_3 x_3_4 x_3_5 x_5_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7041 (t x_0_3 x_2_3 x_3_4 x_3_6 x_3_8 : ℝ) : (¬ (x_3_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7045 (t x_0_3 x_1_2 x_2_3 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7046 (t x_0_4 x_1_2 x_2_4 x_4_5 x_5_8 x_8_9 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7047 (t x_0_4 x_1_4 x_4_5 x_4_8 x_5_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7048 (t x_0_4 x_1_2 x_2_4 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7049 (t x_3_5 x_4_5 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7050 (t x_0_5 x_4_5 x_5_6 x_5_7 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_9)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7051 (t x_0_2 x_2_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7052 (t x_0_4 x_1_2 x_2_4 x_4_5 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7053 (t x_0_5 x_1_2 x_2_5 x_4_5 x_5_7 x_5_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7055 (t x_0_3 x_2_5 x_3_4 x_3_5 x_5_8 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7056 (t x_0_3 x_3_4 x_3_5 x_4_5 x_5_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7057 (t x_0_3 x_1_3 x_3_4 x_3_6 x_3_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7058 (t x_0_1 x_1_2 x_2_3 x_3_8 x_8_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7059 (t x_0_1 x_1_2 x_1_3 x_3_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7060 (t x_0_3 x_3_6 x_3_8 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7061 (t x_0_3 x_1_2 x_2_3 x_3_5 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7065 (t x_0_4 x_0_7 x_1_2 x_2_4 x_4_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7066 (t x_0_4 x_1_2 x_2_4 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7067 (t x_0_1 x_1_6 x_5_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7068 (x_0_2 x_2_7 x_2_8 : ℝ) : (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7069 (x_0_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7070 (t x_0_4 x_1_2 x_2_4 x_4_8 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7071 (t x_0_2 x_1_3 x_2_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7072 (t x_0_1 x_1_6 x_3_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7073 (t x_0_4 x_1_2 x_2_4 x_4_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7074 (t x_0_2 x_2_5 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7075 (t x_4_7 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7076 (t x_0_1 x_0_2 x_1_2 x_2_3 x_2_6 x_3_4 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7077 (t x_0_4 x_1_2 x_2_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7078 (t x_1_2 x_2_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7082 (x_0_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7083 (t x_0_1 x_1_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7084 (t x_2_7 x_3_7 x_5_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_3_7)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7085 (t x_1_6 x_3_6 x_4_5 x_5_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7086 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7087 (t x_0_1 x_1_6 x_2_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7089 (t x_0_2 x_1_2 x_2_4 x_2_5 x_5_6 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7092 (t x_0_2 x_1_2 x_2_4 x_2_8 x_4_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_4_8)) ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7093 (t x_0_2 x_1_2 x_2_4 x_2_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7094 (t x_0_5 x_0_6 x_1_2 x_2_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7095 (t x_0_2 x_2_3 x_3_7 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7096 (t x_0_3 x_1_2 x_2_3 x_3_7 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7101 (t x_2_4 x_3_4 x_4_6 x_4_9 x_6_7 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7103 (t x_0_4 x_1_2 x_2_4 x_4_8 x_8_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7104 (x_3_5 x_4_5 : ℝ) : ((x_3_5 + ((-1) * x_4_5)) ≥ 0) ∨ ((x_3_5 + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory7105 (t x_0_5 x_0_8 x_1_6 x_1_8 x_4_5 x_5_7 x_8_9 : ℝ) : ((t + ((-1) * x_1_6)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7106 (t x_0_4 x_1_2 x_2_4 x_4_6 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7107 (t x_0_1 x_1_3 x_3_7 x_3_9 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7109 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_5 x_5_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7113 (t x_0_1 x_1_6 x_6_7 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7115 (t x_0_3 x_1_3 x_3_5 x_3_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7116 (t x_0_3 x_3_5 x_3_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_3_5 ≥ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7117 (t x_0_3 x_1_3 x_3_4 x_3_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7123 (t x_1_3 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7125 (t x_0_1 x_1_5 x_3_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7128 (t x_0_2 x_0_5 x_1_2 x_2_4 x_2_5 x_5_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7131 (t x_1_2 x_2_4 x_2_6 x_4_6 x_5_6 x_6_9 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7132 (t x_0_4 x_1_2 x_2_4 x_4_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7134 (t x_1_6 x_3_4 x_4_6 x_5_6 x_6_7 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7136 (t x_1_3 x_3_4 x_3_5 x_3_6 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7137 (t x_0_1 x_1_3 x_2_3 x_3_4 x_3_8 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7138 (t x_0_1 x_1_2 x_2_3 x_3_6 x_6_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7139 (t x_0_1 x_1_5 x_2_5 x_5_6 x_5_8 : ℝ) : ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7140 (t x_0_1 x_0_2 x_1_2 x_1_3 x_2_3 x_2_5 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7141 (t x_0_3 x_2_3 x_3_4 x_3_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7142 (t x_0_3 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7147 (t x_0_1 x_1_2 x_2_5 x_3_5 x_5_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7149 (t x_0_2 x_1_2 x_1_5 x_2_3 x_3_5 x_5_6 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7151 (t x_1_4 x_4_5 x_5_6 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7153 (t x_0_1 x_1_2 x_1_3 x_2_3 x_3_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7154 (t x_1_5 x_4_5 x_4_9 x_5_7 x_5_9 x_9_10 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_9)) ≤ 0)) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7155 (t x_3_4 x_3_5 x_4_5 x_5_6 x_5_9 x_6_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7156 (t x_0_1 x_0_2 x_1_2 x_2_3 x_2_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7157 (t x_3_4 x_3_6 x_4_5 x_5_6 x_5_7 x_6_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7158 (x_0_5 x_0_9 x_4_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7159 (t x_0_5 x_3_5 x_4_5 x_5_6 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7160 (t x_0_5 x_3_5 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7161 (t x_0_5 x_3_5 x_5_6 x_5_8 x_8_10 : ℝ) : ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7163 (t x_0_1 x_1_7 x_3_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7165 (t x_0_7 x_1_2 x_2_4 x_2_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7166 (t x_1_2 x_2_4 x_2_5 x_2_6 x_5_6 x_6_9 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7167 (t x_0_5 x_2_3 x_3_5 x_5_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7169 (t x_0_6 x_1_3 x_3_4 x_3_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7170 (t x_0_1 x_1_2 x_1_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7171 (t x_0_3 x_3_4 x_3_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7172 (t x_0_1 x_1_2 x_2_3 x_3_5 x_5_6 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7173 (t x_0_1 x_0_3 x_1_2 x_2_3 x_2_8 x_3_4 x_3_8 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7175 (t x_0_7 x_1_3 x_3_5 x_3_7 x_4_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7178 (t x_0_1 x_0_2 x_1_2 x_1_4 x_2_3 x_2_4 x_4_6 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7181 (t x_0_6 x_1_2 x_2_4 x_2_6 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7184 (t x_1_2 x_2_4 x_2_5 x_5_7 x_7_9 : ℝ) : (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7185 (t x_1_2 x_2_4 x_2_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7186 (t x_0_4 x_4_6 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7191 (t x_0_1 x_1_2 x_2_8 x_8_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7193 (t x_0_6 x_2_3 x_3_6 x_4_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7194 (t x_0_4 x_2_3 x_3_4 x_4_6 x_6_7 x_7_9 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7195 (t x_0_1 x_1_3 x_2_3 x_2_8 x_3_6 x_3_8 x_4_6 x_6_7 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory7197 (t x_3_5 x_4_5 x_4_6 x_5_6 x_5_8 x_6_9 : ℝ) : (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7199 (t x_0_3 x_2_3 x_3_4 x_3_6 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7200 (t x_0_1 x_1_2 x_1_5 x_2_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7201 (t x_1_4 x_2_3 x_3_4 x_4_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7202 (t x_0_4 x_2_3 x_3_4 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7203 (t x_4_6 x_5_6 x_6_7 x_6_9 x_9_10 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7204 (t x_0_1 x_1_2 x_1_3 x_3_5 x_5_6 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7205 (t x_0_1 x_1_2 x_1_5 x_3_5 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7206 (t x_0_1 x_1_2 x_1_3 x_2_3 x_3_4 x_4_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7207 (t x_0_1 x_1_2 x_1_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7210 (t x_2_4 x_4_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7214 (t x_1_5 x_4_7 x_5_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7217 (t x_0_1 x_1_2 x_1_5 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7221 (t x_0_5 x_2_3 x_3_4 x_3_5 x_4_5 x_5_6 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7222 (t x_0_4 x_0_5 x_2_3 x_3_4 x_4_5 x_5_7 x_5_8 : ℝ) : (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7224 (t x_0_1 x_1_5 x_2_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_2_5)) ≤ 0) ∨ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7226 (t x_0_4 x_1_4 x_2_3 x_3_4 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7228 (t x_0_5 x_1_4 x_4_5 x_5_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7229 (t x_0_4 x_1_4 x_4_5 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7230 (t x_0_5 x_1_3 x_3_4 x_3_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7235 (t x_0_4 x_4_5 x_4_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7236 (t x_0_7 x_1_2 x_2_4 x_2_7 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7237 (t x_0_1 x_0_2 x_1_2 x_2_3 x_2_6 x_3_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7240 (t x_0_1 x_0_2 x_1_2 x_1_6 x_2_3 x_3_6 x_6_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7243 (t x_1_2 x_2_5 x_2_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7244 (t x_0_1 x_0_2 x_1_2 x_2_3 x_2_5 x_5_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7245 (t x_0_2 x_1_2 x_2_3 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7246 (t x_1_2 x_2_5 x_2_6 x_4_6 x_6_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7247 (t x_0_4 x_1_4 x_4_5 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7250 (t x_0_6 x_1_3 x_3_4 x_3_6 x_4_6 x_6_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7252 (t x_0_4 x_1_2 x_1_4 x_4_5 x_4_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7254 (t x_0_2 x_2_4 x_4_7 x_5_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7255 (t x_0_6 x_1_3 x_3_4 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7257 (t x_0_5 x_1_3 x_3_5 x_3_8 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7258 (t x_0_3 x_1_3 x_3_4 x_3_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7260 (t x_0_5 x_0_8 x_1_6 x_1_8 x_5_6 x_6_7 x_8_9 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7261 (t x_0_3 x_2_3 x_3_6 x_3_9 x_9_10 : ℝ) : ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7262 (t x_0_2 x_2_4 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7265 (t x_0_2 x_2_6 x_6_8 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7266 (t x_0_6 x_3_4 x_4_5 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7268 (t x_2_4 x_4_6 x_4_8 : ℝ) : (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7271 (t x_0_2 x_0_4 x_2_4 x_4_5 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7272 (t x_0_5 x_0_7 x_1_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7274 (t x_0_3 x_2_3 x_3_5 x_3_7 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7278 (t x_0_1 x_1_5 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7279 (t x_0_1 x_1_6 x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7281 (t x_0_1 x_1_3 x_3_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7283 (t x_0_5 x_1_3 x_3_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7285 (t x_4_5 x_5_6 x_5_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7286 (t x_0_4 x_1_3 x_3_4 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7287 (t x_0_8 x_5_9 x_8_9 : ℝ) : ((t + ((-1) * x_0_8)) ≤ 0) ∨ ((t + x_5_9 + ((-1) * x_8_9)) ≥ 1) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_5_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7289 (t x_0_5 x_5_6 x_5_7 x_6_7 : ℝ) : ((t + ((-1) * x_5_7) + x_6_7) ≥ 1) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory7295 (t x_0_4 x_4_9 x_5_7 x_5_9 x_7_8 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7296 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7297 (t x_1_6 x_2_6 x_4_5 x_5_6 x_5_9 x_6_7 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_2_6)) ≤ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7303 (t x_0_2 x_2_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7304 (t x_0_2 x_2_4 x_2_6 x_4_6 x_6_8 x_6_9 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7305 (t x_0_2 x_2_5 x_2_6 x_3_4 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7309 (t x_0_2 x_1_2 x_2_4 x_2_6 x_2_8 : ℝ) : (¬ (x_2_8 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7313 (t x_2_4 x_4_6 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_2_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7316 (t x_0_5 x_2_5 x_5_6 x_5_7 x_5_9 : ℝ) : ((t + ((-1) * x_5_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7317 (t x_0_1 x_1_2 x_1_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

end ElevenTheory
