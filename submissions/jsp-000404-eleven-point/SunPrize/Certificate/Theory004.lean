import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory995 (x_0_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory997 (x_2_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory998 (x_1_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory999 (x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1000 (x_0_2 x_2_5 x_2_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1002 (x_0_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1003 (x_2_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1004 (x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1005 (x_2_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((x_2_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1007 (x_2_3 x_3_7 x_3_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1008 (x_4_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) ∨ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1010 (x_1_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1012 (x_1_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_3_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1013 (x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1014 (x_1_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1018 (x_1_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1019 (x_5_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1020 (x_1_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1023 (t x_4_8 x_5_8 x_6_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_8) + x_5_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1025 (x_1_6 x_3_6 x_6_10 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1027 (x_1_6 x_2_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_2_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1029 (x_3_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1030 (x_2_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_2_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1031 (x_0_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1033 (x_3_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1034 (x_4_5 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_4_7)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1035 (x_3_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1036 (t x_3_8 x_4_8 x_7_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)) ∨ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1037 (x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1038 (x_0_1 x_0_9 x_1_8 x_1_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_1_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory1039 (x_0_8 x_4_8 x_4_9 x_8_9 : ℝ) : (¬ ((x_4_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory1041 (x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) ∨ ((x_5_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1043 (x_1_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((x_1_2 + ((-1) * x_2_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1044 (x_1_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1045 (x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) ∨ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1046 (x_0_3 x_3_6 x_3_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1048 (x_3_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1049 (x_1_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1050 (x_1_4 x_3_4 : ℝ) : ((x_1_4 + ((-1) * x_3_4)) ≥ 0) ∨ ((x_1_4 + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1051 (x_3_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1052 (x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1053 (x_5_8 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory1055 (x_1_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_1_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1056 (x_1_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1059 (x_2_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_2_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1060 (x_2_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1061 (x_0_3 x_3_4 x_3_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1062 (t x_1_2 x_1_3 x_1_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ ((t + x_1_3 + ((-1) * x_1_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1063 (x_2_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≥ 0)) ∨ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1064 (x_2_3 x_3_5 x_3_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1065 (x_1_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ ((x_1_3 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1067 (x_4_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1068 (x_0_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1070 (t x_5_9 x_6_9 x_8_9 : ℝ) : (¬ ((t + x_5_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ ((t + x_5_9 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1071 (x_0_2 x_2_3 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1072 (x_1_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_1_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1073 (x_0_6 x_3_6 : ℝ) : ((x_0_6 + ((-1) * x_3_6)) ≥ 0) ∨ ((x_0_6 + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1074 (x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_3_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1075 (x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((x_4_9 + ((-1) * x_9_10)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1076 (x_1_3 x_3_4 x_3_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1077 (x_4_5 x_4_6 : ℝ) : ((x_4_5 + ((-1) * x_4_6)) ≤ 0) ∨ ((x_4_5 + ((-1) * x_4_6)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1078 (x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_4_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1079 (x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1081 (x_1_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1083 (x_0_1 x_1_5 x_1_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1084 (x_0_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1086 (x_1_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1087 (x_0_1 x_1_6 x_1_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1089 (x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1090 (t x_0_8 x_0_9 x_8_9 : ℝ) : ((((x_0_8 ≤ x_0_9) ∧ (x_0_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_0_8)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_8) ∧ ((x_0_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_0_8 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_0_8 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_0_8 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : (x_0_8 ≤ x_0_9) ↔ (((1) * x_0_8 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_9 ≤ x_8_9) ↔ (((1) * x_0_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_8_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_0_9 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_9 + ((-1) * x_0_8)) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_9 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_8_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_8 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_0_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_0_8 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_0_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_8 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_8) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1091 (t x_0_2 x_0_8 x_2_8 : ℝ) : ((((x_0_2 ≤ x_0_8) ∧ (x_0_8 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_2_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_2_8)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_2_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_2_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_2) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_8 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_8) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_2 ≤ x_0_8) ↔ (((1) * x_0_2 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_2_8) ↔ (((1) * x_0_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_2 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_8 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1094 (t x_2_6 x_2_7 x_6_7 : ℝ) : ((((x_2_6 ≤ x_2_7) ∧ (x_2_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_2_6 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_2_6 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + x_2_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_2_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_2_7) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_2_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_6 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_6) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_6 ≤ x_2_7) ↔ (((1) * x_2_6 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_7 ≤ x_6_7) ↔ (((1) * x_2_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_7 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_2_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_6 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1095 (t x_0_2 x_0_5 x_2_5 : ℝ) : ((((x_0_2 ≤ x_0_5) ∧ (x_0_5 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_2_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_2_5)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_2_5)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (((x_0_5 + ((-1) * x_2_5)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1)))) := by
  classical
  have e0 : ((t + x_0_2 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_2 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_2_5)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_2 ≤ x_0_5) ↔ (((1) * x_0_2 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_2_5) ↔ (((1) * x_0_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_5 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_5 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_5 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_2_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_2) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_5) + x_2_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1098 (t x_0_5 x_0_6 x_5_6 : ℝ) : ((((x_0_5 ≤ x_0_6) ∧ (x_0_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_5_6)) ≤ ((-1) + t)))) ↔ ((((x_0_5 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_5_6)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) ∧ ((t + x_0_5 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (((x_0_6 + ((-1) * x_5_6)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_5_6) ≥ 1)))) := by
  classical
  have e0 : ((x_0_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_6) + x_5_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_5) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 + ((-1) * x_5_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_5 ≤ x_0_6) ↔ (((1) * x_0_5 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_6 ≤ x_5_6) ↔ (((1) * x_0_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_6 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_6 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_5 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) ↔ (((1) * x_0_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_5 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_6 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1099 (t x_1_5 x_1_8 x_5_8 : ℝ) : ((((x_1_5 ≤ x_1_8) ∧ (x_1_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_5_8)) ≤ ((-1) + t)))) ↔ ((((x_1_5 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1)) ∧ ((t + x_1_5 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_5_8) ≥ 1)))) := by
  classical
  have e0 : (x_1_5 ≤ x_1_8) ↔ (((1) * x_1_5 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_5_8) ↔ (((1) * x_1_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_1_8 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_8 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_8 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_5_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_5 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_5 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_5 + ((-1) * x_5_8)) ≤ (-1)) ↔ (((1) * x_1_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_1_5 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_1_8 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_5 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_5) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_8) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1100 (t x_6_7 x_6_8 x_7_8 : ℝ) : ((((x_6_7 ≤ x_6_8) ∧ (x_6_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_6_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_6_8) ∧ (x_6_8 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_6_7 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_6_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_6_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1) ∧ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_6_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_6_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_7 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_6_7) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_6_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_6_8) ↔ (((1) * x_6_7 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_7_8) ↔ (((1) * x_6_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_7_8 ≤ x_6_8) ↔ (¬ (((1) * x_6_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_6_8 ≤ x_6_7) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_8 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_7 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_6_7 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_6_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_6_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_6_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1101 (t x_5_6 x_5_8 x_6_8 : ℝ) : ((((x_5_6 ≤ x_5_8) ∧ (x_5_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_5_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_5_6 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_5_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_5_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_5_6) + x_5_8) ≥ 1) ∧ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_5_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_5_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_5_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_5_6 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_5_8) ↔ (((1) * x_5_6 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_8 ≤ x_6_8) ↔ (((1) * x_5_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_8 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_5_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_6 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_5_6) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_5_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1102 (t x_1_5 x_1_6 x_5_6 : ℝ) : ((((x_1_5 ≤ x_1_6) ∧ (x_1_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_5_6)) ≤ ((-1) + t)))) ↔ ((((x_1_5 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_5_6)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1)) ∧ ((t + x_1_5 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (((x_1_6 + ((-1) * x_5_6)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_1_6) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_5_6) ≥ 1)))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_6 + ((-1) * x_5_6)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_5 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_5) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_6) + x_5_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_5 ≤ x_1_6) ↔ (((1) * x_1_5 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_5_6) ↔ (((1) * x_1_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_6 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_6 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_5 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_5 + ((-1) * x_5_6)) ≤ (-1)) ↔ (((1) * x_1_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_5 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1103 (t x_0_1 x_0_5 x_1_5 : ℝ) : ((((x_0_1 ≤ x_0_5) ∧ (x_0_5 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_1_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_1_5)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_1_5)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_1_5)) ≥ 1)) ∨ (((x_0_5 + ((-1) * x_1_5)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_5)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_1_5) ≥ 1)))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_5)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_1 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_5 + ((-1) * x_1_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_1 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_5 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_5) ↔ (((1) * x_0_1 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_1_5) ↔ (((1) * x_0_5 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_5 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_5 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_1_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_1) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_5) + x_1_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1104 (t x_0_5 x_0_8 x_5_8 : ℝ) : ((((x_0_5 ≤ x_0_8) ∧ (x_0_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_5_8)) ≤ ((-1) + t)))) ↔ ((((x_0_5 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1)) ∧ ((t + x_0_5 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_5_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_5 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_8 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_5 + ((-1) * x_5_8)) ≤ (-1)) ↔ (((1) * x_0_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_8 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_5 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_5 ≤ x_0_8) ↔ (((1) * x_0_5 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_5_8) ↔ (((1) * x_0_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_5 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_5 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_5) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_8) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1105 (t x_0_5 x_4_5 x_4_6 x_5_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1106 (t x_0_4 x_0_5 x_4_5 : ℝ) : ((((x_0_4 ≤ x_0_5) ∧ (x_0_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_4_5)) ≤ ((-1) + t)))) ↔ ((((x_0_4 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_4_5)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (((x_0_5 + ((-1) * x_4_5)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_4_5) ≥ 1)))) := by
  classical
  have e0 : ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_4) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_5) + x_4_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 + ((-1) * x_4_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_4 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_4 ≤ x_0_5) ↔ (((1) * x_0_4 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_5 ≤ x_4_5) ↔ (((1) * x_0_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_0_5 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_5 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_4 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_5 + ((-1) * x_4_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_0_4 + ((-1) * x_4_5)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_4 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1107 (t x_0_1 x_0_3 x_1_3 : ℝ) : ((((x_0_1 ≤ x_0_3) ∧ (x_0_3 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_3 + ((-1) * x_0_3)) ≤ ((-1) + t))) ∨ ((x_1_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_0_3 + ((-1) * x_1_3)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_3)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_1_3)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1) ∧ ((t + x_0_3 + ((-1) * x_1_3)) ≥ 1)) ∨ (((x_0_3 + ((-1) * x_1_3)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_3)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_1 + ((-1) * x_0_3)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_3) + x_1_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_1) + x_0_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_1_3)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_3) ↔ (((1) * x_0_1 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_3 ≤ x_1_3) ↔ (((1) * x_0_3 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_3 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_3 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_3 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_3 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_3 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_3)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_3 + ((-1) * x_1_3)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_1_3)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_3 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1110 (t x_3_7 x_3_8 x_7_8 : ℝ) : ((((x_3_7 ≤ x_3_8) ∧ (x_3_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_3_7 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_3_7 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + x_3_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_3_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_3_8) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : (x_3_7 ≤ x_3_8) ↔ (((1) * x_3_7 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_7_8) ↔ (((1) * x_3_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_7_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_3_8 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_8 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_8 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_7_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_7 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_3_7 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_3_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_3_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_3_7 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_3_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_3_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_7 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_7) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1111 (t x_5_6 x_5_7 x_6_7 : ℝ) : ((((x_5_6 ≤ x_5_7) ∧ (x_5_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_5_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_5_7) ∧ (x_5_7 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_5_6 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_5_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + x_5_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_5_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_5_6) + x_5_7) ≥ 1) ∧ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_5_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_5_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_5_6) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_5_7) ↔ (((1) * x_5_6 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_6_7) ↔ (((1) * x_5_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_7 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_7 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_6 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_5_6 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_5_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_5_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_5_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1113 (t x_3_5 x_3_6 x_5_6 : ℝ) : ((((x_3_5 ≤ x_3_6) ∧ (x_3_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_3_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_5_6)) ≤ ((-1) + t)))) ↔ ((((x_3_5 + ((-1) * x_3_6)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_5_6)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_6)) ≥ 1) ∧ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (((x_3_6 + ((-1) * x_5_6)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_6)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_6) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)))) := by
  classical
  have e0 : ((t + ((-1) * x_3_6) + x_5_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_6 + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 + ((-1) * x_5_6)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_5 + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * x_3_5 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_5 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_5 ≤ x_3_6) ↔ (((1) * x_3_5 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_6 ≤ x_5_6) ↔ (((1) * x_3_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_6 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_3_6 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_6 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_5_6)) ≥ 0) ↔ (¬ (((1) * x_3_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_3_5 + ((-1) * x_3_6)) ≥ 0) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_5) + x_3_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1114 (t x_3_6 x_3_7 x_6_7 : ℝ) : ((((x_3_6 ≤ x_3_7) ∧ (x_3_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_3_6 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_3_6 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_3_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_3_7) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_3_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_6) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_6 ≤ x_3_7) ↔ (((1) * x_3_6 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_7 ≤ x_6_7) ↔ (((1) * x_3_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_7 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_6 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_3_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_3_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_6 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1115 (t x_0_6 x_0_7 x_6_7 : ℝ) : ((((x_0_6 ≤ x_0_7) ∧ (x_0_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_0_6 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_6) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_6 ≤ x_0_7) ↔ (((1) * x_0_6 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_6_7) ↔ (((1) * x_0_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_7 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_6 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1118 (t x_0_3 x_0_6 x_3_6 : ℝ) : ((((x_0_3 ≤ x_0_6) ∧ (x_0_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_3_6)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_3_6)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_3_6)) ≥ 1)) ∨ (((x_0_6 + ((-1) * x_3_6)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_3_6) ≥ 1)))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_3_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_3 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_3) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_6) + x_3_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_6) ↔ (((1) * x_0_3 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_6 ≤ x_3_6) ↔ (((1) * x_0_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_6 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_3_6)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_3 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_6 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1119 (t x_0_7 x_0_8 x_7_8 : ℝ) : ((((x_0_7 ≤ x_0_8) ∧ (x_0_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_0_7 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_0_7 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_0_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_7 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_7 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_7 ≤ x_0_8) ↔ (((1) * x_0_7 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_7_8) ↔ (((1) * x_0_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_8 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_7 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_7) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1120 (t x_4_6 x_4_8 x_6_8 : ℝ) : ((((x_4_6 ≤ x_4_8) ∧ (x_4_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_4_6 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_4_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + x_4_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_4_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_4_8) ≥ 1) ∧ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_4_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_4_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_6 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_4_6 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_4_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_4_8) ↔ (((1) * x_4_6 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_6_8) ↔ (((1) * x_4_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_4_8 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_4_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_6 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_4_6) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_4_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1121 (t x_6_8 x_6_9 x_8_9 : ℝ) : ((((x_6_8 ≤ x_6_9) ∧ (x_6_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_6_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_6_8 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_6_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_6_8 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_6_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_6_8 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_6_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_6_8) + x_6_9) ≥ 1) ∧ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_6_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_8 ≤ x_6_9) ↔ (((1) * x_6_8 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_6_9 ≤ x_8_9) ↔ (((1) * x_6_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_8_9 ≤ x_6_9) ↔ (¬ (((1) * x_6_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : (x_6_9 ≤ x_6_8) ↔ (¬ (((1) * x_6_8 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 + ((-1) * x_6_8)) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_6_9 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_8_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_8 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_6_8 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_6_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_6_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_6_8 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_6_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_8 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_6_8 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_6_8) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_6_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1122 (t x_4_5 x_4_8 x_5_8 : ℝ) : ((((x_4_5 ≤ x_4_8) ∧ (x_4_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_5_8)) ≤ ((-1) + t)))) ↔ ((((x_4_5 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_4_8 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1)) ∧ ((t + x_4_5 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + x_4_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (((x_4_8 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + ((-1) * x_4_5) + x_4_8) ≥ 1) ∧ ((t + ((-1) * x_4_8) + x_5_8) ≥ 1)))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_8 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_4_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_5 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_5) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_8) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_5 ≤ x_4_8) ↔ (((1) * x_4_5 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_8 ≤ x_5_8) ↔ (((1) * x_4_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_8 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_4_5 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_4_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_5 + ((-1) * x_5_8)) ≤ (-1)) ↔ (((1) * x_4_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_5 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_8 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1123 (x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1124 (t x_0_6 x_0_8 x_6_8 : ℝ) : ((((x_0_6 ≤ x_0_8) ∧ (x_0_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_0_6 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_6) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_6 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_6 ≤ x_0_8) ↔ (((1) * x_0_6 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_6_8) ↔ (((1) * x_0_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_6 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1125 (t x_6_7 x_6_9 x_7_9 : ℝ) : ((((x_6_7 ≤ x_6_9) ∧ (x_6_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_6_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_6_7 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_6_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_6_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_6_7) + x_6_9) ≥ 1) ∧ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_6_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_6_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_6_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_6_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_7 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_6_7 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_7 ≤ x_6_9) ↔ (((1) * x_6_7 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_7_9) ↔ (((1) * x_6_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_6_9) ↔ (¬ (((1) * x_6_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_9 ≤ x_6_7) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_9 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_6_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_7 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_6_7) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_6_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1126 (t x_1_4 x_1_5 x_4_5 : ℝ) : ((((x_1_4 ≤ x_1_5) ∧ (x_1_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_4_5)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_5)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_4_5)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_5)) ≥ 1) ∧ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (((x_1_5 + ((-1) * x_4_5)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_5)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_5) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_5)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_4 + ((-1) * x_1_5)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_5 + ((-1) * x_4_5)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_4 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_4 ≤ x_1_5) ↔ (((1) * x_1_4 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_5 ≤ x_4_5) ↔ (((1) * x_1_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_5 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_5 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_4_5)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_1_5)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_4) + x_1_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_5) + x_4_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1127 (t x_4_7 x_4_9 x_7_9 : ℝ) : ((((x_4_7 ≤ x_4_9) ∧ (x_4_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_4_7 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_4_7 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + x_4_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_4_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_4_7) + x_4_9) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_4_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_4_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_7 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_7) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_7 ≤ x_4_9) ↔ (((1) * x_4_7 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_9 ≤ x_7_9) ↔ (((1) * x_4_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_9 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_7 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_7 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_4_7 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_4_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_4_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_7 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1128 (t x_4_5 x_4_7 x_5_7 : ℝ) : ((((x_4_5 ≤ x_4_7) ∧ (x_4_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_4_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_5_7)) ≤ ((-1) + t)))) ↔ ((((x_4_5 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_4_7 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) ∧ ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (((x_4_7 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1) ∧ ((t + ((-1) * x_4_7) + x_5_7) ≥ 1)))) := by
  classical
  have e0 : (x_4_5 ≤ x_4_7) ↔ (((1) * x_4_5 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_7 ≤ x_5_7) ↔ (((1) * x_4_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_7 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_4_7 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_7 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_7 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_5_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_4_5 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_4_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) ↔ (((1) * x_4_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_7 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_4_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_5 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_4_5) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_4_7) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1129 (t x_3_4 x_3_7 x_4_5 x_4_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1130 (t x_3_4 x_3_7 x_4_7 : ℝ) : ((((x_3_4 ≤ x_3_7) ∧ (x_3_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_4_7)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + x_3_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (((x_3_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_4_7) ≥ 1)))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_7 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_3_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_4) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_7) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_3_7) ↔ (((1) * x_3_4 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_7 ≤ x_4_7) ↔ (((1) * x_3_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_7 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_3_4 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_3_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1131 (t x_3_7 x_3_9 x_7_9 : ℝ) : ((((x_3_7 ≤ x_3_9) ∧ (x_3_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_3_7 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_3_7 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_3_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_7 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_7) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_7 ≤ x_3_9) ↔ (((1) * x_3_7 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_7_9) ↔ (((1) * x_3_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_9 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_7 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_7 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_3_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_7 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1132 (t x_7_8 x_7_9 x_8_9 : ℝ) : ((((x_7_8 ≤ x_7_9) ∧ (x_7_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_7_9 + ((-1) * x_7_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_7_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_7_9) ∧ (x_7_9 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_7_8 + ((-1) * x_7_9)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_7_8 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_7_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_7_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_7_8 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_7_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_7_8) + x_7_9) ≥ 1) ∧ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((t + ((-1) * x_7_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_7_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_7_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_7_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_7_8 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_8 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_7_9) ↔ (((1) * x_7_8 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_8_9) ↔ (((1) * x_7_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_8_9 ≤ x_7_9) ↔ (¬ (((1) * x_7_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_7_9 ≤ x_7_8) ↔ (¬ (((1) * x_7_8 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_9 + ((-1) * x_7_8)) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_8 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_8 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_8 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_7_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_7_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_7_8 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_7_8 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_7_8) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_8 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1133 (t x_0_4 x_0_8 x_4_8 : ℝ) : ((((x_0_4 ≤ x_0_8) ∧ (x_0_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_4_8)) ≤ ((-1) + t)))) ↔ ((((x_0_4 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_4_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_4) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_8) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_4 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_4 ≤ x_0_8) ↔ (((1) * x_0_4 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_4_8) ↔ (((1) * x_0_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_8 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_4 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_4 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1136 (t x_1_4 x_1_6 x_4_6 : ℝ) : ((((x_1_4 ≤ x_1_6) ∧ (x_1_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_4_6)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (((x_1_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_6) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_4 ≤ x_1_6) ↔ (((1) * x_1_4 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_4_6) ↔ (((1) * x_1_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_6 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_4 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1139 (t x_1_4 x_1_8 x_4_8 : ℝ) : ((((x_1_4 ≤ x_1_8) ∧ (x_1_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_4_8)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_4_8) ≥ 1)))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_4 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_1_4 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_4 ≤ x_1_8) ↔ (((1) * x_1_4 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_4_8) ↔ (((1) * x_1_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_8 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_8 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_4) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_8) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1140 (t x_4_8 x_4_9 x_8_9 : ℝ) : ((((x_4_8 ≤ x_4_9) ∧ (x_4_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_4_8 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_4_8 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + x_4_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_4_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_4_8 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_4_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_4_8) + x_4_9) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_4_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_4_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_8 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_4_8 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_8) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_8 ≤ x_4_9) ↔ (((1) * x_4_8 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_9 ≤ x_8_9) ↔ (((1) * x_4_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_9 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_9 + ((-1) * x_4_8)) ≥ 1) ↔ (((1) * x_4_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_8 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_4_8 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_4_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_4_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_8 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1141 (t x_3_4 x_3_5 x_4_5 : ℝ) : ((((x_3_4 ≤ x_3_5) ∧ (x_3_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_3_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_3_5) ∧ (x_3_5 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_4_5)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_5)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_4_5)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1) ∧ ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (((x_3_5 + ((-1) * x_4_5)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_5)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_4_5)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_5 + ((-1) * x_4_5)) ≤ 0) ↔ (((1) * x_3_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * x_3_4 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_3_5) ↔ (((1) * x_3_4 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_5 ≤ x_4_5) ↔ (((1) * x_3_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_5 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_5 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_5 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_5 + ((-1) * x_4_5)) ≥ 0) ↔ (¬ (((1) * x_3_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_4 + ((-1) * x_3_5)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_4) + x_3_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_5) + x_4_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1142 (t x_4_6 x_4_7 x_6_7 : ℝ) : ((((x_4_6 ≤ x_4_7) ∧ (x_4_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_4_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_4_6 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_4_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_4_6 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_4_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_4_7) ≥ 1) ∧ ((t + ((-1) * x_4_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_4_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_6) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_6 ≤ x_4_7) ↔ (((1) * x_4_6 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_7 ≤ x_6_7) ↔ (((1) * x_4_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_7 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_7 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_6 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_6 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_4_6 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_4_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_4_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_6 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1143 (t x_4_5 x_4_6 x_5_6 : ℝ) : ((((x_4_5 ≤ x_4_6) ∧ (x_4_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_4_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_4_6) ∧ (x_4_6 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_5_6)) ≤ ((-1) + t)))) ↔ ((((x_4_5 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_5_6)) ≤ 0) ∧ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1)) ∧ ((t + x_4_5 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (((x_4_6 + ((-1) * x_5_6)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1)))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_5 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 + ((-1) * x_5_6)) ≥ 0) ↔ (¬ (((1) * x_4_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_4_5 ≤ x_4_6) ↔ (((1) * x_4_5 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : (x_4_6 ≤ x_5_6) ↔ (((1) * x_4_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_6 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_6 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_4_5 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * x_4_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_5_6)) ≤ (-1)) ↔ (((1) * x_4_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((t + x_4_5 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_4_5) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_4_6) + x_5_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1144 (t x_0_4 x_0_6 x_4_5 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1145 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((((x_0_4 ≤ x_0_6) ∧ (x_0_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_4_6)) ≤ ((-1) + t)))) ↔ ((((x_0_4 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (((x_0_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_4) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_4 ≤ x_0_6) ↔ (((1) * x_0_4 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_6 ≤ x_4_6) ↔ (((1) * x_0_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_6 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_4 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_4 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1148 (x_0_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1149 (t x_0_6 x_3_4 x_3_6 x_4_5 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1150 (t x_0_2 x_0_4 x_2_4 : ℝ) : ((((x_0_2 ≤ x_0_4) ∧ (x_0_4 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_2_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_2_4)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_4)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_2_4)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1) ∧ ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (((x_0_4 + ((-1) * x_2_4)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_4)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_4) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)))) := by
  classical
  have e0 : (x_0_2 ≤ x_0_4) ↔ (((1) * x_0_2 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_2_4) ↔ (((1) * x_0_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_0_4 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_4 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_4 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_4 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_2 + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_4 + ((-1) * x_2_4)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_2_4)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_2_4)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_0_4)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_2) + x_0_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_4) + x_2_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1151 (t x_0_1 x_0_2 x_1_2 : ℝ) : ((((x_0_1 ≤ x_0_2) ∧ (x_0_2 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_2 + ((-1) * x_0_2)) ≤ ((-1) + t))) ∨ ((x_1_2 ≤ x_0_2) ∧ (x_0_2 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_0_2 + ((-1) * x_1_2)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_2)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_1_2)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_2)) ≥ 1) ∧ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (((x_0_2 + ((-1) * x_1_2)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_2)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_2)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_1_2)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_1_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_1) + x_0_2) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_2) + x_1_2) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_1 + ((-1) * x_1_2)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_1 + ((-1) * x_0_2)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_2) ↔ (((1) * x_0_1 + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_2 ≤ x_1_2) ↔ (((1) * x_0_2 + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_2 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_1_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_2 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_2 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_2 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_2 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_2 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_2)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_2 + ((-1) * x_1_2)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_1_2)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_2 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_1 + ((-1) * x_0_2)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1152 (t x_2_5 x_2_8 x_5_8 : ℝ) : ((((x_2_5 ≤ x_2_8) ∧ (x_2_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_5_8)) ≤ ((-1) + t)))) ↔ ((((x_2_5 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_5_8) ≥ 1)))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_8 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_5) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_8) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_2_8) ↔ (((1) * x_2_5 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_5_8) ↔ (((1) * x_2_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_8 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_5_8)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_5 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_8 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1153 (t x_2_3 x_2_4 x_3_4 : ℝ) : ((((x_2_3 ≤ x_2_4) ∧ (x_2_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_2_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_2_4) ∧ (x_2_4 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_3_4)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_4)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_3_4)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1) ∧ ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (((x_2_4 + ((-1) * x_3_4)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_4)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_3_4)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_3 + ((-1) * x_2_4)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_3) + x_2_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_4) + x_3_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_3 ≤ x_2_4) ↔ (((1) * x_2_3 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_4 ≤ x_3_4) ↔ (((1) * x_2_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_4 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_4 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_4 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_4 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_4)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_4 + ((-1) * x_3_4)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_3 + ((-1) * x_3_4)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_4 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1154 (t x_0_4 x_0_5 x_3_4 x_4_5 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1155 (t x_1_3 x_1_6 x_3_6 : ℝ) : ((((x_1_3 ≤ x_1_6) ∧ (x_1_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_3_6)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_3_6)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + x_1_6 + ((-1) * x_3_6)) ≥ 1)) ∨ (((x_1_6 + ((-1) * x_3_6)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_6) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_3_6) ≥ 1)))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_6)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_3 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_1_6 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_3 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_6 + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_3 ≤ x_1_6) ↔ (((1) * x_1_3 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_3_6) ↔ (((1) * x_1_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_6 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_3_6)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_3) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_6) + x_3_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1156 (t x_0_3 x_0_4 x_3_4 : ℝ) : ((((x_0_3 ≤ x_0_4) ∧ (x_0_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_3_4)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_4)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_3_4)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_4)) ≥ 1) ∧ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (((x_0_4 + ((-1) * x_3_4)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_4)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_4) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_3_4) ≥ 1)))) := by
  classical
  have e0 : ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_3 + ((-1) * x_0_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_3_4)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_4) ↔ (((1) * x_0_3 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_4 ≤ x_3_4) ↔ (((1) * x_0_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_4 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_4 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_4 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_4 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_3_4)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_0_4)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_3) + x_0_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_4) + x_3_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1159 (t x_3_6 x_3_8 x_6_8 : ℝ) : ((((x_3_6 ≤ x_3_8) ∧ (x_3_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_3_6 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_3_6 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + x_3_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_3_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_3_8) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_3_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_6 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_6) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_6 ≤ x_3_8) ↔ (((1) * x_3_6 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_8 ≤ x_6_8) ↔ (((1) * x_3_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_8 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_6 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_3_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_3_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_6 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1160 (t x_2_3 x_2_7 x_3_7 : ℝ) : ((((x_2_3 ≤ x_2_7) ∧ (x_2_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_3_7)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + x_2_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (((x_2_7 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_7) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_3_7) ≥ 1)))) := by
  classical
  have e0 : (x_2_3 ≤ x_2_7) ↔ (((1) * x_2_3 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_7 ≤ x_3_7) ↔ (((1) * x_2_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_2_7 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_7 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_3 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_7 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_3_7)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_2_7 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_3 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_3) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_7) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1161 (t x_0_2 x_0_3 x_2_3 : ℝ) : ((((x_0_2 ≤ x_0_3) ∧ (x_0_3 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_3 + ((-1) * x_0_3)) ≤ ((-1) + t))) ∨ ((x_2_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_0_3 + ((-1) * x_2_3)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_3)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_2_3)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1) ∧ ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (((x_0_3 + ((-1) * x_2_3)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_3)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_2_3)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_2 + ((-1) * x_2_3)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_0_3)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_2 ≤ x_0_3) ↔ (((1) * x_0_2 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_3 ≤ x_2_3) ↔ (((1) * x_0_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_3 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_3 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_3 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_3 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_3 + ((-1) * x_2_3)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_0_3)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_2) + x_0_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_3) + x_2_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1162 (x_1_2 x_2_3 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1163 (t x_1_2 x_1_7 x_2_7 : ℝ) : ((((x_1_2 ≤ x_1_7) ∧ (x_1_7 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_2_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_2_7)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_2_7) ≥ 1)))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_7)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_2 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_2 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_2 ≤ x_1_7) ↔ (((1) * x_1_2 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_2_7) ↔ (((1) * x_1_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_7 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_2) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_7) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1164 (t x_2_7 x_2_8 x_7_8 : ℝ) : ((((x_2_7 ≤ x_2_8) ∧ (x_2_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_2_7 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_2_7 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((x_2_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_7 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_7) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_7 ≤ x_2_8) ↔ (((1) * x_2_7 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_7_8) ↔ (((1) * x_2_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_8 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_8 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_7 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_2_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_7 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1165 (t x_1_3 x_1_4 x_3_4 : ℝ) : ((((x_1_3 ≤ x_1_4) ∧ (x_1_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_1_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_3_4)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_4)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_3_4)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_4)) ≥ 1) ∧ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (((x_1_4 + ((-1) * x_3_4)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_4)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_4) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_1_4)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_4 + ((-1) * x_3_4)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_3_4)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_3 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_3 ≤ x_1_4) ↔ (((1) * x_1_3 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_4 ≤ x_3_4) ↔ (((1) * x_1_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_4 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_4 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_4 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_4 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_4 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_4 + ((-1) * x_3_4)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_1_4)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_3) + x_1_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_4) + x_3_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1166 (x_1_3 x_3_4 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1167 (t x_1_2 x_1_3 x_2_3 : ℝ) : ((((x_1_2 ≤ x_1_3) ∧ (x_1_3 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_3 + ((-1) * x_1_3)) ≤ ((-1) + t))) ∨ ((x_2_3 ≤ x_1_3) ∧ (x_1_3 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_1_3 + ((-1) * x_2_3)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_3)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_2_3)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1) ∧ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (((x_1_3 + ((-1) * x_2_3)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_3)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_2) + x_1_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_2_3)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_2 + ((-1) * x_1_3)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_3) + x_2_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_2 ≤ x_1_3) ↔ (((1) * x_1_2 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_3 ≤ x_2_3) ↔ (((1) * x_1_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_3 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_3 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_3 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_3 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_3)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_3 + ((-1) * x_2_3)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_2_3)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1170 (t x_0_2 x_1_2 x_1_3 x_2_3 x_3_7 : ℝ) : (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1171 (t x_7_10 x_7_9 x_9_10 : ℝ) : ((((x_7_9 ≤ x_7_10) ∧ (x_7_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_7_10 + ((-1) * x_7_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_7_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_7_9 + ((-1) * x_7_10)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_7_9 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_7_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_7_9 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + x_7_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_7_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_7_9 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_7_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_7_9) + x_7_10) ≥ 1) ∧ ((t + ((-1) * x_7_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_7_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_7_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_7_9 + ((-1) * x_7_10)) ≥ 0) ↔ (((1) * x_7_10 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_7_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_7_9) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_7_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_9 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_10 ≤ x_9_10) ↔ (((1) * x_7_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_7_10 ≤ x_7_9) ↔ (((1) * x_7_10 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_7_9)) ≥ 1) ↔ (((1) * x_7_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_9 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_9 + ((-1) * x_7_10)) ≤ 0) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_7_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_7_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_7_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_7_9 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_7_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1172 (t x_1_8 x_6_7 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1173 (t x_0_2 x_0_6 x_2_6 : ℝ) : ((((x_0_2 ≤ x_0_6) ∧ (x_0_6 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_2_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_2_6)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1)) ∨ (((x_0_6 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_2_6) ≥ 1)))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_2 + ((-1) * x_2_6)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_2 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_6 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_2 ≤ x_0_6) ↔ (((1) * x_0_2 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_2_6) ↔ (((1) * x_0_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_0_6 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_6 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_6 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_2) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_6) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1176 (t x_0_2 x_1_3 x_2_3 x_2_6 x_3_6 : ℝ) : (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1177 (t x_2_3 x_2_6 x_3_6 : ℝ) : ((((x_2_3 ≤ x_2_6) ∧ (x_2_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_3_6)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_3_6)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + x_2_6 + ((-1) * x_3_6)) ≥ 1)) ∨ (((x_2_6 + ((-1) * x_3_6)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_6) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_3_6) ≥ 1)))) := by
  classical
  have e0 : ((x_2_6 + ((-1) * x_3_6)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_3 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_3) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_6) + x_3_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_3 ≤ x_2_6) ↔ (((1) * x_2_3 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_3_6) ↔ (((1) * x_2_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_6 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_6 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_3 + ((-1) * x_3_6)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_3 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_6 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1178 (t x_0_1 x_0_3 x_1_2 x_1_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1179 (t x_0_3 x_0_7 x_3_7 : ℝ) : ((((x_0_3 ≤ x_0_7) ∧ (x_0_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_3_7)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_3_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_3) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_7) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_7) ↔ (((1) * x_0_3 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_3_7) ↔ (((1) * x_0_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_7 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_7 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_3_7)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_3 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_7 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1180 (t x_0_2 x_2_3 x_2_4 x_3_4 x_3_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1181 (t x_2_6 x_2_8 x_6_8 : ℝ) : ((((x_2_6 ≤ x_2_8) ∧ (x_2_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_2_6 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_2_6 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_2_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_6 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_6 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_6 ≤ x_2_8) ↔ (((1) * x_2_6 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_6_8) ↔ (((1) * x_2_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_8 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_6 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_6 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_6) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1182 (t x_1_2 x_1_6 x_2_6 : ℝ) : ((((x_1_2 ≤ x_1_6) ∧ (x_1_6 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_2_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_2_6)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + x_1_6 + ((-1) * x_2_6)) ≥ 1)) ∨ (((x_1_6 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_6) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_2_6) ≥ 1)))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_6) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_1_2) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_6 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_2 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_2 ≤ x_1_6) ↔ (((1) * x_1_2 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_2_6) ↔ (((1) * x_1_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_6 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_2_6)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_2 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_6 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1183 (t x_1_2 x_1_5 x_2_5 : ℝ) : ((((x_1_2 ≤ x_1_5) ∧ (x_1_5 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_2_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_2_5)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_5)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_2_5)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1) ∧ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (((x_1_5 + ((-1) * x_2_5)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_5)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_5) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_2_5) ≥ 1)))) := by
  classical
  have e0 : (x_1_2 ≤ x_1_5) ↔ (((1) * x_1_2 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_2_5) ↔ (((1) * x_1_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_1_5 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_5 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_5 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_2 + ((-1) * x_1_5)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_5 + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_2_5)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_2_5)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_1_5)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_2) + x_1_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_5) + x_2_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1184 (t x_2_4 x_2_5 x_4_5 : ℝ) : ((((x_2_4 ≤ x_2_5) ∧ (x_2_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_2_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_4_5)) ≤ ((-1) + t)))) ↔ ((((x_2_4 + ((-1) * x_2_5)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_4_5)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_5)) ≥ 1) ∧ ((t + x_2_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (((x_2_5 + ((-1) * x_4_5)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_5)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_5) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_5 + ((-1) * x_4_5)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_5)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_4) + x_2_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_2_5) + x_4_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_4 ≤ x_2_5) ↔ (((1) * x_2_4 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_5 ≤ x_4_5) ↔ (((1) * x_2_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_5 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_2_5 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_5 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_5 + ((-1) * x_4_5)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_4 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_5 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1185 (t x_2_5 x_2_6 x_5_6 : ℝ) : ((((x_2_5 ≤ x_2_6) ∧ (x_2_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_5_6)) ≤ ((-1) + t)))) ↔ ((((x_2_5 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_5_6)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (((x_2_6 + ((-1) * x_5_6)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_6) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_5_6) ≥ 1)))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_6 + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_5 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_2_6) ↔ (((1) * x_2_5 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_5_6) ↔ (((1) * x_2_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_6 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_6 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_6 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_5 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_5_6)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_5) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_6) + x_5_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1186 (t x_2_5 x_2_7 x_5_7 : ℝ) : ((((x_2_5 ≤ x_2_7) ∧ (x_2_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_5_7)) ≤ ((-1) + t)))) ↔ ((((x_2_5 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + x_2_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (((x_2_7 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_7) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_5_7) ≥ 1)))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_7 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_5) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_7) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_2_7) ↔ (((1) * x_2_5 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_7 ≤ x_5_7) ↔ (((1) * x_2_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_7 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_5 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_7 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1187 (t x_0_5 x_1_2 x_2_5 x_2_7 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1188 (t x_5_7 x_5_8 x_7_8 : ℝ) : ((((x_5_7 ≤ x_5_8) ∧ (x_5_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_5_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_5_7 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_5_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_5_7 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + x_5_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_5_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_5_7) + x_5_8) ≥ 1) ∧ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_5_7 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_5_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_7 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_7) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_5_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_5_8) ↔ (((1) * x_5_7 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_7_8) ↔ (((1) * x_5_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_7_8 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_5_8 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_8 + ((-1) * x_5_7)) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_5_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_5_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_5_7 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_5_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1190 (t x_1_5 x_1_7 x_5_7 : ℝ) : ((((x_1_5 ≤ x_1_7) ∧ (x_1_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_5_7)) ≤ ((-1) + t)))) ↔ ((((x_1_5 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1)) ∧ ((t + x_1_5 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_5_7) ≥ 1)))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_5 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_5) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_7) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_5 ≤ x_1_7) ↔ (((1) * x_1_5 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_5_7) ↔ (((1) * x_1_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_5 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_5 + ((-1) * x_5_7)) ≤ (-1)) ↔ (((1) * x_1_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_5 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_7 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1191 (t x_3_5 x_3_7 x_5_7 : ℝ) : ((((x_3_5 ≤ x_3_7) ∧ (x_3_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_5_7)) ≤ ((-1) + t)))) ↔ ((((x_3_5 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + x_3_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (((x_3_7 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_7) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_5_7) ≥ 1)))) := by
  classical
  have e0 : ((x_3_7 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_3_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_5 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_5) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_7) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_5 ≤ x_3_7) ↔ (((1) * x_3_5 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_7 ≤ x_5_7) ↔ (((1) * x_3_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_7 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_3_5 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_3_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_5 + ((-1) * x_5_7)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_5 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_7 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1192 (t x_4_7 x_4_8 x_7_8 : ℝ) : ((((x_4_7 ≤ x_4_8) ∧ (x_4_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_4_7 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_4_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_4_7 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + x_4_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_4_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_4_7) + x_4_8) ≥ 1) ∧ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((x_4_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_4_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_7 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_7) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_7 ≤ x_4_8) ↔ (((1) * x_4_7 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_8 ≤ x_7_8) ↔ (((1) * x_4_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_8 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_8 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_7 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_7 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_4_7 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_4_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_4_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_7 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1193 (t x_1_4 x_1_7 x_4_7 : ℝ) : ((((x_1_4 ≤ x_1_7) ∧ (x_1_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_4_7)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_4_7) ≥ 1)))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_4 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_4 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_4 ≤ x_1_7) ↔ (((1) * x_1_4 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_4_7) ↔ (((1) * x_1_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_4) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_7) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1197 (t x_0_3 x_0_5 x_3_5 : ℝ) : ((((x_0_3 ≤ x_0_5) ∧ (x_0_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_3_5)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_3_5)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (((x_0_5 + ((-1) * x_3_5)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_3_5) ≥ 1)))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_5)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_3 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_5) ↔ (((1) * x_0_3 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_3_5) ↔ (((1) * x_0_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_5 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_5 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_5 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_3_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_3) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_5) + x_3_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1200 (x_3_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1201 (x_0_3 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1202 (t x_0_3 x_3_5 x_3_6 x_4_5 x_5_6 : ℝ) : (¬ ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1203 (t x_1_5 x_1_9 x_5_9 : ℝ) : ((((x_1_5 ≤ x_1_9) ∧ (x_1_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_5_9)) ≤ ((-1) + t)))) ↔ ((((x_1_5 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1)) ∧ ((t + x_1_5 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_5_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_5_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_9 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_5 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_5) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_9) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_5 ≤ x_1_9) ↔ (((1) * x_1_5 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_5_9) ↔ (((1) * x_1_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_5 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_5 + ((-1) * x_5_9)) ≤ (-1)) ↔ (((1) * x_1_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_5 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_9 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1204 (t x_4_5 x_4_9 x_5_9 : ℝ) : ((((x_4_5 ≤ x_4_9) ∧ (x_4_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_5_9)) ≤ ((-1) + t)))) ↔ ((((x_4_5 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1)) ∧ ((t + x_4_5 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + x_4_9 + ((-1) * x_5_9)) ≥ 1)) ∨ (((x_4_9 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_5_9) ≥ 1)))) := by
  classical
  have e0 : ((t + x_4_5 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_4_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_5 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_5) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_4_9) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_5 ≤ x_4_9) ↔ (((1) * x_4_5 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_5_9) ↔ (((1) * x_4_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_4_9 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_5 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_5 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_4_5 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_9 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_4_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_4_5 + ((-1) * x_5_9)) ≤ (-1)) ↔ (((1) * x_4_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_9 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1205 (t x_1_3 x_1_5 x_3_5 : ℝ) : ((((x_1_3 ≤ x_1_5) ∧ (x_1_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_3_5)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_5)) ≤ 0) ∧ ((x_1_5 + ((-1) * x_3_5)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_5)) ≥ 1) ∧ ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (((x_1_5 + ((-1) * x_3_5)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_5)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_5) ≥ 1) ∧ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1)))) := by
  classical
  have e0 : ((t + x_1_3 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_1_5)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_5 + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * x_1_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_3 + ((-1) * x_3_5)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_3 ≤ x_1_5) ↔ (((1) * x_1_3 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_5 ≤ x_3_5) ↔ (((1) * x_1_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_5 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_5 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_5 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_3_5)) ≥ 0) ↔ (¬ (((1) * x_1_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_1_5)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_3) + x_1_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_5) + x_3_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1206 (t x_2_3 x_2_8 x_3_8 : ℝ) : ((((x_2_3 ≤ x_2_8) ∧ (x_2_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_3_8)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_3_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_3_8) ≥ 1)))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_3 + ((-1) * x_3_8)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_3 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_3 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_8 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_3 ≤ x_2_8) ↔ (((1) * x_2_3 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_3_8) ↔ (((1) * x_2_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_8 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_3 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_3 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_3) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_8) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1207 (t x_3_4 x_3_6 x_4_6 : ℝ) : ((((x_3_4 ≤ x_3_6) ∧ (x_3_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_3_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_4_6)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_6)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1) ∧ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (((x_3_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_6)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_6) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_3_6)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_4 + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * x_3_4 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_4 ≤ x_3_6) ↔ (((1) * x_3_4 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_6 ≤ x_4_6) ↔ (((1) * x_3_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_6 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_3_6 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_6 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_3_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_4) + x_3_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1208 (t x_1_3 x_1_7 x_3_7 : ℝ) : ((((x_1_3 ≤ x_1_7) ∧ (x_1_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_3_7)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_3_7) ≥ 1)))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_3 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_3 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_3 ≤ x_1_7) ↔ (((1) * x_1_3 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_3_7) ↔ (((1) * x_1_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_7 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_3) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_7) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1211 (t x_1_3 x_3_4 x_3_7 x_4_6 x_4_7 : ℝ) : (¬ ((t + ((-1) * x_4_6) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1212 (x_0_3 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1213 (t x_0_5 x_1_3 x_2_3 x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1214 (t x_0_5 x_0_7 x_5_7 : ℝ) : ((((x_0_5 ≤ x_0_7) ∧ (x_0_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_5_7)) ≤ ((-1) + t)))) ↔ ((((x_0_5 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_5_7)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1)) ∧ ((t + x_0_5 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_5_7)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_5_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_5 + ((-1) * x_5_7)) ≤ (-1)) ↔ (((1) * x_0_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_7 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_7 + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_0_7) ↔ (((1) * x_0_5 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_7 ≤ x_5_7) ↔ (((1) * x_0_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_0_7 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_7 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_7 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_5 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_5_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_5 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_5) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_7) + x_5_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1215 (x_0_3 x_3_4 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1216 (t x_0_3 x_0_4 x_3_4 x_3_6 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1217 (t x_1_6 x_1_8 x_6_8 : ℝ) : ((((x_1_6 ≤ x_1_8) ∧ (x_1_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_6_8)) ≤ ((-1) + t)))) ↔ ((((x_1_6 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_6_8)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_6_8)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_6_8) ≥ 1)))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_8)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_8 + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_6 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_6 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_8 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_6 ≤ x_1_8) ↔ (((1) * x_1_6 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_6_8) ↔ (((1) * x_1_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_8 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_6_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_6 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_6) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_8) + x_6_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1218 (t x_1_8 x_1_9 x_8_9 : ℝ) : ((((x_1_8 ≤ x_1_9) ∧ (x_1_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_1_8)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_8) ∧ ((x_1_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_1_8 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_1_8 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_1_8 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_1_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_8) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_1_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_1_9) ↔ (((1) * x_1_8 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_8_9) ↔ (((1) * x_1_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_8_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_1_9 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_9 + ((-1) * x_1_8)) ≥ 1) ↔ (((1) * x_1_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_9 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_8 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_8 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1219 (t x_1_7 x_1_8 x_5_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1220 (t x_3_4 x_3_8 x_4_8 : ℝ) : ((((x_3_4 ≤ x_3_8) ∧ (x_3_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_4_8)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + x_3_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (((x_3_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_8) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_4_8) ≥ 1)))) := by
  classical
  have e0 : ((t + x_3_4 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_8 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_3_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_4) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_3_8) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_4 ≤ x_3_8) ↔ (((1) * x_3_4 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_4_8) ↔ (((1) * x_3_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_3_8 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_4 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_3_4 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_3_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_3_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1221 (t x_0_1 x_0_6 x_1_6 : ℝ) : ((((x_0_1 ≤ x_0_6) ∧ (x_0_6 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_1_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_1_6)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_1_6)) ≥ 1)) ∨ (((x_0_6 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_1_6) ≥ 1)))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_1 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_6) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_1) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_6) ↔ (((1) * x_0_1 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_6 ≤ x_1_6) ↔ (((1) * x_0_6 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_6 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_6 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_1_6)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_1 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_6 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1222 (x_0_1 x_1_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1223 (t x_0_2 x_1_3 x_2_3 x_2_4 x_3_4 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1224 (t x_2_5 x_2_9 x_5_9 : ℝ) : ((((x_2_5 ≤ x_2_9) ∧ (x_2_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_5_9)) ≤ ((-1) + t)))) ↔ ((((x_2_5 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_5_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_5_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_9)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_9 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_5 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_9 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_2_9) ↔ (((1) * x_2_5 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_5_9) ↔ (((1) * x_2_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_5 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_5) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_9) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1225 (t x_3_5 x_3_9 x_5_9 : ℝ) : ((((x_3_5 ≤ x_3_9) ∧ (x_3_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_5_9)) ≤ ((-1) + t)))) ↔ ((((x_3_5 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_5_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_5_9) ≥ 1)))) := by
  classical
  have e0 : ((x_3_5 + ((-1) * x_5_9)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_9 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_5 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_3_5 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_9 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_5 ≤ x_3_9) ↔ (((1) * x_3_5 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_5_9) ↔ (((1) * x_3_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_9 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_5 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_5) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_9) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1226 (t x_5_6 x_5_9 x_6_9 : ℝ) : ((((x_5_6 ≤ x_5_9) ∧ (x_5_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_5_6 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_5_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_5_6 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + x_5_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_5_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_5_6) + x_5_9) ≥ 1) ∧ ((t + ((-1) * x_5_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((t + ((-1) * x_5_6) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_5_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_5_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_6 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_5_6 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_5_6 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_5_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_6 ≤ x_5_9) ↔ (((1) * x_5_6 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_6_9) ↔ (((1) * x_5_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_5_9 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_9 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_6 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_5_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_5_6 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_5_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1227 (t x_2_3 x_2_5 x_3_5 : ℝ) : ((((x_2_3 ≤ x_2_5) ∧ (x_2_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_2_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_3_5)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_5)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_3_5)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_5)) ≥ 1) ∧ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (((x_2_5 + ((-1) * x_3_5)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_5)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_5) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_3_5) ≥ 1)))) := by
  classical
  have e0 : ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_3 + ((-1) * x_2_5)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 + ((-1) * x_3_5)) ≥ 0) ↔ (¬ (((1) * x_2_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_3) + x_2_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_2_5) + x_3_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_3 ≤ x_2_5) ↔ (((1) * x_2_3 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_5 ≤ x_3_5) ↔ (((1) * x_2_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_5 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_2_5 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_5 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_5 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_3 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_3 + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * x_2_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_2_3 + ((-1) * x_3_5)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_3 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1228 (t x_5_8 x_5_9 x_8_9 : ℝ) : ((((x_5_8 ≤ x_5_9) ∧ (x_5_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_5_8 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_5_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_5_8 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + x_5_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_5_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_5_8 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_5_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_5_8) + x_5_9) ≥ 1) ∧ ((t + ((-1) * x_5_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_5_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_5_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_8 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_5_8 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_5_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_5_8) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_8 ≤ x_5_9) ↔ (((1) * x_5_8 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_8_9) ↔ (((1) * x_5_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_8_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_5_9 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_9 + ((-1) * x_5_8)) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_8 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_8 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_5_8 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_5_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_5_8 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_5_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1229 (t x_3_5 x_3_8 x_5_8 : ℝ) : ((((x_3_5 ≤ x_3_8) ∧ (x_3_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_5_8)) ≤ ((-1) + t)))) ↔ ((((x_3_5 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_5_8)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + x_3_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (((x_3_8 + ((-1) * x_5_8)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_8) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_5_8) ≥ 1)))) := by
  classical
  have e0 : ((x_3_8 + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * x_3_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_5 + ((-1) * x_5_8)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_3_5 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_3_5 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_8 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_5 ≤ x_3_8) ↔ (((1) * x_3_5 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_8 ≤ x_5_8) ↔ (((1) * x_3_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_8 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_5_8)) ≥ 0) ↔ (¬ (((1) * x_3_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_5 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_5) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_8) + x_5_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1230 (t x_0_3 x_0_8 x_3_8 : ℝ) : ((((x_0_3 ≤ x_0_8) ∧ (x_0_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_3_8)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_3_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_3_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_3 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_8 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_8 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_8) ↔ (((1) * x_0_3 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_3_8) ↔ (((1) * x_0_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_3) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_8) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1233 (t x_0_3 x_1_6 x_3_6 x_3_8 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((t + x_1_6 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1234 (t x_1_3 x_1_8 x_3_8 : ℝ) : ((((x_1_3 ≤ x_1_8) ∧ (x_1_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_3_8)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_3_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_3_8) ≥ 1)))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_8)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_3 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_8 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_3 ≤ x_1_8) ↔ (((1) * x_1_3 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_3_8) ↔ (((1) * x_1_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_8 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_3) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_8) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1235 (t x_1_4 x_3_7 x_4_7 x_4_9 x_7_9 : ℝ) : (¬ ((x_4_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1236 (t x_2_4 x_2_7 x_4_7 : ℝ) : ((((x_2_4 ≤ x_2_7) ∧ (x_2_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_4_7)) ≤ ((-1) + t)))) ↔ ((((x_2_4 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + x_2_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (((x_2_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_7) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_4_7) ≥ 1)))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_7 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_4) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_7) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_4 ≤ x_2_7) ↔ (((1) * x_2_4 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_7 ≤ x_4_7) ↔ (((1) * x_2_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_7 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_4 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1237 (t x_2_5 x_5_8 x_5_9 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1238 (x_0_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1239 (t x_0_5 x_0_9 x_5_9 : ℝ) : ((((x_0_5 ≤ x_0_9) ∧ (x_0_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_5_9)) ≤ ((-1) + t)))) ↔ ((((x_0_5 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1)) ∧ ((t + x_0_5 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_5_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_5_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_9 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_9 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 + ((-1) * x_5_9)) ≤ (-1)) ↔ (((1) * x_0_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_5 ≤ x_0_9) ↔ (((1) * x_0_5 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_5_9) ↔ (((1) * x_0_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_5 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_5 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_5) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_9) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1240 (t x_1_4 x_1_9 x_4_9 : ℝ) : ((((x_1_4 ≤ x_1_9) ∧ (x_1_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_4_9)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_4_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_9)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_4 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_1_9 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_9 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_4 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_4 ≤ x_1_9) ↔ (((1) * x_1_4 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_4_9) ↔ (((1) * x_1_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_9 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_4) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1243 (t x_5_7 x_5_9 x_7_9 : ℝ) : ((((x_5_7 ≤ x_5_9) ∧ (x_5_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_5_7 + ((-1) * x_5_9)) ≤ 0) ∧ ((x_5_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_5_7 + ((-1) * x_5_9)) ≥ 1) ∧ ((t + x_5_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_5_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_5_9)) ≥ 0) ∧ ((x_5_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_5_7) + x_5_9) ≥ 1) ∧ ((t + ((-1) * x_5_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_5_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_7 + ((-1) * x_5_9)) ≥ 0) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_5_7) + x_5_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_7 ≤ x_5_9) ↔ (((1) * x_5_7 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_9 ≤ x_7_9) ↔ (((1) * x_5_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_9 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_5_7)) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_7 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_7 + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * x_5_7 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_5_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_5_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_5_7 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_5_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1244 (t x_4_7 x_4_8 x_5_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1246 (t x_3_8 x_3_9 x_8_9 : ℝ) : ((((x_3_8 ≤ x_3_9) ∧ (x_3_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_3_8 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_3_8 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_3_8 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_3_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_3_9) ↔ (((1) * x_3_8 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_9 ≤ x_8_9) ↔ (((1) * x_3_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_8_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : (x_3_9 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 + ((-1) * x_3_8)) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_9 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_8_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_8 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_8 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_3_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_3_8 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_3_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_8 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_8 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_8) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1247 (t x_0_8 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_0_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1248 (t x_8_10 x_8_9 x_9_10 : ℝ) : ((((x_8_9 ≤ x_8_10) ∧ (x_8_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_8_10 + ((-1) * x_8_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_8_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_8_10) ∧ (x_8_10 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_8_9 + ((-1) * x_8_10)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_8_9 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_8_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_8_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_8_9 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_8_9) + x_8_10) ≥ 1) ∧ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_8_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_8_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_8_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_8_9 + ((-1) * x_8_10)) ≥ 0) ↔ (((1) * x_8_10 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_8_9) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_8_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_8_9 ≤ x_8_10) ↔ (¬ (((1) * x_8_10 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_9_10) ↔ (((1) * x_8_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_8_10) ↔ (¬ (((1) * x_8_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_8_10 ≤ x_8_9) ↔ (((1) * x_8_10 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_8_9)) ≥ 1) ↔ (((1) * x_8_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_10 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_8_9 + ((-1) * x_8_10)) ≤ 0) ↔ (¬ (((1) * x_8_10 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_8_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_8_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_8_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_8_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1249 (t x_4_8 x_4_9 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1250 (t x_4_10 x_4_9 x_9_10 : ℝ) : ((((x_4_9 ≤ x_4_10) ∧ (x_4_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_4_9 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_4_9 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_4_9 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_4_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 + ((-1) * x_4_10)) ≥ 0) ↔ (((1) * x_4_10 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_9) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_9 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_9_10) ↔ (((1) * x_4_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_10 ≤ x_4_9) ↔ (((1) * x_4_10 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_4_9)) ≥ 1) ↔ (((1) * x_4_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_9 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_4_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_9 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1251 (t x_0_3 x_0_9 x_3_9 : ℝ) : ((((x_0_3 ≤ x_0_9) ∧ (x_0_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_3_9)) ≤ ((-1) + t)))) ↔ ((((x_0_3 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_3_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_9)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_9 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_3 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_9 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_3 ≤ x_0_9) ↔ (((1) * x_0_3 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_3_9) ↔ (((1) * x_0_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_3 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_3) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_9) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1254 (t x_0_3 x_3_8 x_3_9 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1255 (x_4_8 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1256 (x_0_3 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

end ElevenTheory
