import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory7709 (t x_0_3 x_0_6 x_1_2 x_2_3 x_3_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7710 (t x_0_3 x_1_2 x_2_3 x_3_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7711 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7714 (t x_0_2 x_2_6 x_6_8 x_6_9 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7715 (t x_0_4 x_1_2 x_2_4 x_3_4 x_4_6 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7716 (t x_0_3 x_0_7 x_1_2 x_2_3 x_3_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7717 (t x_0_3 x_1_2 x_2_3 x_3_5 x_5_8 x_8_9 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7718 (t x_0_4 x_4_8 x_4_9 x_6_8 x_8_9 : ℝ) : (¬ ((x_4_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory7719 (t x_5_7 x_6_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7720 (t x_0_3 x_0_4 x_1_2 x_2_3 x_3_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7724 (t x_0_2 x_1_2 x_2_5 x_2_6 x_5_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7728 (t x_0_1 x_1_2 x_1_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7729 (t x_0_5 x_1_6 x_5_6 : ℝ) : (¬ (x_1_6 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1) ∨ ((t + ((-1) * x_0_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7732 (x_3_6 x_4_6 x_5_6 : ℝ) : (¬ ((x_3_6 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_3_6 + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7733 (t x_0_3 x_0_4 x_3_4 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7734 (t x_0_3 x_3_5 x_4_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7735 (t x_0_3 x_3_4 x_4_5 x_5_8 x_8_9 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7736 (t x_1_4 x_3_4 x_4_5 x_4_9 x_5_8 : ℝ) : ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7737 (t x_0_3 x_3_5 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7738 (t x_0_2 x_0_3 x_0_6 x_1_2 x_1_3 x_2_6 x_3_4 x_4_8 x_6_7 x_6_8 x_7_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ (x_8_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  linarith

theorem theory7741 (t x_0_8 x_3_4 x_4_6 x_4_8 x_8_10 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_0_8 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7742 (t x_0_1 x_1_2 x_1_5 x_2_5 x_5_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7745 (t x_1_2 x_2_6 x_6_7 x_7_8 x_8_10 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7747 (t x_1_2 x_2_6 x_6_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7749 (x_0_3 x_1_3 x_3_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7750 (t x_1_9 x_3_4 x_4_6 x_4_9 x_9_10 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_1_9 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7752 (t x_2_6 x_5_9 x_6_7 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_5_9)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7754 (t x_0_5 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7757 (t x_0_1 x_1_6 x_1_8 x_2_5 x_2_8 x_5_7 x_8_9 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7758 (t x_0_1 x_1_3 x_1_5 x_4_5 x_5_8 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7761 (t x_0_4 x_4_6 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7764 (x_0_5 x_0_9 x_4_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7766 (t x_0_2 x_1_2 x_2_4 x_2_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7767 (t x_0_3 x_0_6 x_1_2 x_2_3 x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7768 (t x_1_2 x_2_3 x_2_6 : ℝ) : ((t + ((-1) * x_2_6)) ≤ 0) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + x_2_3 + ((-1) * x_2_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7769 (x_0_2 x_2_5 x_2_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7771 (t x_0_5 x_1_2 x_2_3 x_2_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7772 (t x_0_4 x_2_4 x_4_5 x_4_7 x_7_8 : ℝ) : (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7773 (t x_0_2 x_2_6 x_2_9 x_3_6 x_6_7 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7776 (t x_1_2 x_2_5 x_2_7 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7777 (t x_2_3 x_2_7 x_3_5 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7778 (t x_0_1 x_1_2 x_1_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7780 (t x_0_8 x_2_5 x_5_7 x_5_8 x_8_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_8)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7782 (t x_0_2 x_0_5 x_2_6 x_5_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7783 (t x_0_6 x_5_6 x_5_7 x_6_7 x_6_8 x_7_9 : ℝ) : ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7784 (t x_3_4 x_4_5 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7785 (t x_0_1 x_1_6 x_1_9 x_4_9 x_9_10 : ℝ) : (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_1_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ ((t + ((-1) * x_4_9)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7786 (t x_3_4 x_4_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7790 (t x_0_6 x_4_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7791 (t x_0_4 x_3_4 x_4_6 x_4_7 x_5_6 x_6_7 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7795 (t x_0_4 x_3_4 x_4_5 x_4_7 x_7_9 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7796 (t x_1_3 x_1_4 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7797 (t x_0_1 x_1_4 x_1_7 x_7_8 x_8_9 : ℝ) : (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7800 (t x_0_3 x_0_5 x_3_5 x_3_6 x_5_6 x_5_7 x_6_8 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7801 (t x_1_4 x_4_5 x_4_6 x_5_6 x_6_8 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7803 (t x_0_1 x_1_2 x_2_8 x_6_8 x_8_9 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7804 (t x_1_2 x_1_6 x_2_8 : ℝ) : ((t + ((-1) * x_1_6)) ≤ 0) ∨ ((t + x_1_2 + ((-1) * x_1_6)) ≥ 1) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ (x_2_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7805 (x_1_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7808 (t x_0_2 x_0_6 x_1_6 x_2_4 x_2_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7810 (t x_0_6 x_2_6 x_3_5 x_5_8 x_5_9 x_6_7 x_6_9 : ℝ) : (¬ ((x_5_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7811 (x_1_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((x_1_4 + ((-1) * x_4_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7812 (t x_0_6 x_2_3 x_3_6 x_4_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7813 (x_2_5 x_3_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((x_3_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7817 (t x_0_4 x_2_4 x_4_6 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7818 (t x_0_4 x_3_4 x_4_6 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7820 (t x_3_4 x_4_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7821 (t x_0_4 x_1_2 x_2_3 x_2_4 x_4_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7823 (t x_0_2 x_2_4 x_2_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7824 (t x_0_1 x_1_4 x_4_6 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7825 (t x_0_1 x_1_6 x_2_5 x_2_6 x_5_8 x_6_10 : ℝ) : (¬ (x_5_8 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7826 (t x_1_6 x_3_4 x_3_5 x_4_5 x_4_6 x_5_6 x_5_7 x_6_10 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory7828 (t x_0_4 x_0_5 x_1_5 x_1_6 x_4_6 x_5_9 x_6_7 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7829 (t x_0_1 x_1_4 x_4_5 x_5_6 x_6_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7830 (t x_0_3 x_1_3 x_3_6 x_3_7 x_7_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7831 (t x_0_4 x_0_5 x_2_3 x_3_4 x_4_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7834 (t x_0_3 x_1_2 x_2_3 x_3_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7836 (t x_0_3 x_1_3 x_3_7 x_3_9 x_9_10 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7837 (t x_0_5 x_2_3 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7838 (t x_0_2 x_0_6 x_2_6 x_6_7 x_6_8 x_8_10 : ℝ) : ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7840 (t x_0_5 x_0_6 x_1_6 x_3_5 x_3_7 x_5_6 x_5_7 x_6_7 x_6_9 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory7842 (t x_0_7 x_0_8 x_1_2 x_2_3 x_2_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7845 (t x_1_2 x_1_4 x_2_5 x_3_4 x_4_5 x_4_9 x_5_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7846 (t x_0_2 x_0_5 x_1_5 x_2_4 x_2_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7847 (t x_0_6 x_3_6 x_3_9 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_0_6 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7848 (t x_0_1 x_1_4 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7849 (t x_0_1 x_1_2 x_1_7 x_2_5 x_5_6 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7850 (t x_0_7 x_3_4 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_7)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7852 (t x_0_1 x_1_4 x_1_6 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7853 (t x_0_1 x_1_3 x_1_6 x_3_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_1_6 ≥ 0)) ∨ ((t + x_1_6 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory7854 (t x_0_2 x_0_3 x_3_7 x_5_7 x_7_10 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7855 (t x_0_2 x_2_3 x_2_6 x_3_7 x_7_8 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7856 (t x_0_1 x_1_4 x_1_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7858 (t x_1_4 x_3_4 x_4_6 x_4_9 x_6_7 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7861 (t x_0_1 x_1_2 x_1_9 x_2_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_1_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7862 (t x_2_3 x_3_4 x_3_7 x_4_7 x_7_10 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_4_7 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7863 (t x_0_2 x_0_3 x_0_4 x_2_3 x_2_7 x_3_4 x_3_7 x_4_6 x_6_9 x_7_10 x_9_10 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory7865 (t x_0_2 x_2_3 x_3_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7867 (t x_0_1 x_1_4 x_1_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7868 (t x_0_2 x_0_3 x_0_4 x_2_3 x_3_5 x_3_9 x_4_6 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory7869 (t x_0_4 x_4_6 x_6_9 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7870 (t x_0_6 x_0_8 x_2_3 x_3_4 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7874 (t x_0_1 x_1_2 x_1_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7875 (t x_1_2 x_2_3 x_2_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7876 (t x_0_1 x_0_4 x_1_4 x_1_6 x_4_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7878 (t x_0_4 x_3_4 x_4_5 x_4_8 x_5_6 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7879 (t x_0_2 x_1_2 x_2_3 x_2_4 x_4_5 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7881 (t x_0_2 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7883 (t x_0_3 x_2_3 x_3_5 x_3_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7884 (t x_0_3 x_2_3 x_3_5 x_3_9 x_5_9 x_9_10 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_3_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7887 (t x_1_8 x_2_4 x_4_5 x_4_8 x_8_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_1_8 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7889 (t x_0_3 x_0_6 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_6) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory7891 (t x_0_1 x_1_2 x_2_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7894 (t x_0_3 x_2_3 x_3_4 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7897 (t x_0_4 x_1_4 x_2_3 x_3_4 x_4_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7899 (t x_0_4 x_1_2 x_2_3 x_2_4 x_3_4 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7900 (t x_0_4 x_0_5 x_1_2 x_2_3 x_2_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7902 (t x_2_4 x_4_5 x_4_8 x_5_8 x_8_10 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7903 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_8 x_8_9 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7906 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7909 (t x_0_2 x_1_2 x_2_4 x_2_7 x_2_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_2_7)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_2_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7910 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7913 (t x_0_3 x_3_5 x_3_6 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + x_3_5 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7915 (t x_0_1 x_1_2 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7916 (t x_0_7 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_7 ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7918 (x_1_2 x_2_3 x_2_5 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7919 (t x_1_2 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7922 (t x_2_4 x_4_6 x_4_7 x_6_7 x_7_10 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7924 (t x_0_3 x_3_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7926 (t x_1_4 x_2_4 x_2_9 x_4_6 x_4_9 x_9_10 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7927 (t x_0_2 x_0_3 x_2_4 x_3_6 x_4_5 x_5_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory7929 (t x_0_1 x_0_8 x_1_3 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7935 (x_2_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7936 (t x_0_1 x_1_2 x_1_5 x_4_5 x_5_6 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7944 (t x_0_7 x_2_6 x_3_4 x_4_6 x_4_7 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7947 (t x_0_2 x_2_3 x_2_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7948 (t x_0_3 x_0_4 x_4_6 x_5_6 x_6_10 x_6_7 : ℝ) : ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7951 (x_0_5 x_0_6 x_0_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_0_7)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory7953 (t x_2_6 x_4_5 x_5_6 x_5_7 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7955 (t x_0_4 x_3_4 x_4_5 x_4_6 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_4_9)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7957 (t x_0_2 x_0_6 x_6_8 x_7_8 x_8_10 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7960 (t x_0_3 x_3_8 x_5_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7963 (t x_0_1 x_1_3 x_1_8 x_4_8 x_5_8 x_8_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7967 (t x_2_5 x_3_5 x_5_6 : ℝ) : ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_2_5) + x_3_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7968 (t x_0_2 x_0_3 x_2_8 x_3_5 x_5_6 x_6_10 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + x_6_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7969 (t x_0_2 x_0_4 x_0_7 x_2_7 x_2_8 x_3_4 x_4_6 x_4_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory7971 (t x_0_1 x_0_4 x_1_2 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7974 (t x_0_4 x_1_6 x_3_4 x_4_6 x_4_7 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory7976 (t x_0_3 x_2_3 x_3_5 x_3_8 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((t + ((-1) * x_3_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7979 (t x_0_4 x_2_3 x_3_4 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7980 (t x_0_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory7981 (t x_0_4 x_0_5 x_1_4 x_2_3 x_3_4 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory7982 (t x_0_1 x_1_2 x_2_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7986 (t x_0_3 x_1_3 x_2_3 x_3_4 x_3_5 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7987 (t x_0_3 x_2_3 x_3_4 x_3_6 x_6_8 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7988 (t x_0_1 x_0_2 x_1_6 x_2_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7989 (t x_0_1 x_0_2 x_1_2 x_2_5 x_2_6 x_5_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7992 (t x_0_4 x_2_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7995 (t x_0_5 x_1_5 x_5_6 x_5_8 x_6_7 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7996 (t x_0_1 x_1_2 x_1_7 x_2_9 x_7_8 : ℝ) : (¬ (x_2_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory7997 (t x_0_1 x_0_4 x_1_2 x_2_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory7999 (t x_0_5 x_4_5 x_5_6 x_5_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8004 (t x_0_4 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8007 (t x_0_1 x_1_3 x_1_6 x_1_7 x_5_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8010 (t x_0_1 x_1_4 x_1_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8011 (t x_4_7 x_4_9 x_7_9 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_4_9 ≥ 0)) ∨ ((t + ((-1) * x_4_7) + x_4_9) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8012 (t x_0_3 x_2_3 x_3_4 x_3_9 x_4_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_4_9)) ≤ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8014 (t x_0_2 x_2_4 x_3_4 x_4_5 x_4_6 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8015 (t x_0_7 x_2_3 x_3_5 x_3_7 x_5_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8016 (t x_0_3 x_2_4 x_3_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8017 (t x_0_6 x_2_3 x_3_5 x_3_6 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8018 (t x_0_2 x_0_3 x_3_7 x_6_7 x_7_10 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8019 (t x_0_4 x_3_4 x_4_5 x_4_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8020 (t x_0_4 x_3_4 x_4_5 x_4_8 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8021 (t x_0_2 x_0_5 x_1_2 x_1_5 x_2_3 x_3_4 x_4_9 x_5_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory8022 (t x_0_6 x_1_6 x_2_3 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ (x_1_6 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8023 (t x_0_6 x_2_3 x_3_5 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8024 (t x_0_3 x_2_3 x_3_4 x_3_6 x_3_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8027 (t x_0_8 x_0_9 x_1_9 x_2_3 x_3_5 x_3_8 x_5_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_1_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory8031 (t x_0_3 x_2_3 x_3_7 x_3_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8035 (t x_1_6 x_1_7 x_5_6 x_6_7 x_6_8 x_7_10 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8036 (x_0_1 x_1_7 x_1_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8037 (t x_0_4 x_0_6 x_4_6 x_4_7 x_5_7 x_6_8 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8038 (t x_0_5 x_5_6 x_6_8 x_8_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8042 (t x_0_1 x_1_2 x_1_7 x_2_5 x_2_7 x_7_8 : ℝ) : ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8043 (t x_0_6 x_5_6 x_5_8 x_6_8 x_6_9 x_8_10 : ℝ) : (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8045 (t x_0_1 x_1_2 x_1_6 : ℝ) : ((t + ((-1) * x_1_6)) ≤ 0) ∨ ((t + x_1_2 + ((-1) * x_1_6)) ≥ 1) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory8046 (t x_0_4 x_2_3 x_3_4 x_4_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8047 (t x_0_6 x_1_6 x_2_3 x_3_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8052 (t x_0_4 x_2_3 x_3_4 x_4_5 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8053 (t x_0_3 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8054 (t x_0_3 x_2_3 x_3_4 x_3_7 x_7_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8055 (t x_0_3 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8058 (x_2_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8059 (x_2_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory8061 (t x_0_1 x_1_5 x_1_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8062 (t x_0_1 x_1_4 x_1_5 x_4_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_5)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory8064 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_8 x_4_7 x_7_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_7_8)) ≤ 0)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory8066 (t x_0_2 x_0_5 x_1_2 x_1_5 x_2_4 x_3_4 x_4_6 x_4_9 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory8068 (t x_2_4 x_3_4 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory8074 (t x_0_2 x_0_3 x_2_3 x_3_4 x_3_8 x_4_8 x_8_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

end ElevenTheory
