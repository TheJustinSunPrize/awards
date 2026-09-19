import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory5527 (t x_1_2 x_2_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5528 (t x_0_4 x_1_4 x_1_7 x_4_7 x_4_9 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5530 (t x_0_1 x_1_2 x_2_6 x_2_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5533 (t x_0_1 x_1_2 x_1_3 x_3_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5538 (t x_2_5 x_2_7 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_2_5 ≥ 0)) ∨ ((t + ((-1) * x_2_7)) ≤ 0) ∨ ((t + ((-1) * x_2_7) + x_5_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5541 (t x_0_3 x_3_4 x_4_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5543 (t x_0_3 x_3_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5544 (t x_0_4 x_0_6 x_3_6 x_6_7 x_6_9 x_9_10 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5545 (t x_0_4 x_0_6 x_3_5 x_3_6 x_4_5 x_5_8 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5546 (t x_0_2 x_1_2 x_2_3 x_2_5 x_3_5 x_5_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5548 (t x_0_4 x_1_2 x_2_3 x_2_4 x_4_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5553 (t x_0_6 x_4_6 x_6_7 x_6_8 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_9 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5558 (t x_0_1 x_1_2 x_2_3 x_3_5 x_5_6 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5560 (t x_0_4 x_1_2 x_2_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5566 (t x_0_3 x_3_4 x_3_7 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_7)) ≤ 0) ∨ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5567 (t x_4_5 x_4_8 x_5_6 : ℝ) : ((t + x_4_5 + ((-1) * x_4_8)) ≥ 1) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_4_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5571 (t x_0_3 x_0_4 x_1_2 x_2_3 x_3_4 x_4_7 x_4_8 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5572 (t x_0_2 x_0_3 x_0_5 x_1_2 x_1_3 x_2_5 x_3_4 x_4_7 x_4_9 x_5_6 x_5_8 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  linarith

theorem theory5573 (t x_0_2 x_0_3 x_0_5 x_1_2 x_1_3 x_2_5 x_3_4 x_4_7 x_5_6 x_5_8 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory5581 (t x_0_4 x_4_5 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5582 (t x_2_5 x_3_6 x_5_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_2_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5584 (t x_3_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5587 (t x_0_5 x_2_5 x_5_6 x_5_8 x_5_9 : ℝ) : ((t + ((-1) * x_5_9)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5588 (t x_0_1 x_1_2 x_1_4 x_2_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5592 (t x_0_3 x_2_3 x_3_4 x_3_5 x_3_7 : ℝ) : ((t + ((-1) * x_3_7)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5593 (t x_0_2 x_2_4 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_9)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5594 (t x_0_2 x_0_5 x_2_5 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5595 (t x_0_4 x_3_4 x_3_5 x_4_5 x_4_7 x_5_9 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5597 (t x_0_4 x_0_5 x_4_5 x_5_7 x_5_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5598 (t x_0_5 x_4_6 x_5_6 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ (x_0_5 ≥ 0)) ∨ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5599 (t x_0_2 x_1_2 x_2_4 x_2_5 x_4_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ (x_4_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5601 (x_4_9 x_5_10 x_5_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_5_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5603 (t x_1_6 x_2_4 x_3_6 x_4_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_2_4 ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5606 (t x_0_1 x_1_3 x_1_9 x_3_4 x_3_9 x_4_8 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5609 (t x_0_3 x_3_6 x_4_6 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5611 (t x_0_4 x_2_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5613 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5615 (t x_0_1 x_1_3 x_1_7 x_1_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5616 (t x_0_1 x_1_3 x_1_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5617 (t x_0_1 x_1_3 x_1_4 x_3_4 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5618 (t x_2_3 x_3_5 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5619 (t x_0_1 x_1_4 x_1_5 x_5_6 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ (x_1_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5620 (t x_0_1 x_0_5 x_1_4 x_4_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((t + ((-1) * x_5_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5627 (t x_0_1 x_1_2 x_2_4 x_4_6 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5628 (t x_0_2 x_2_5 x_5_7 x_7_8 x_8_10 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_10)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5629 (t x_0_2 x_2_4 x_4_6 x_4_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5630 (t x_2_6 x_4_6 x_6_8 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_2_6 ≥ 0)) ∨ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5631 (t x_0_3 x_3_4 x_4_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5638 (t x_0_3 x_3_4 x_4_7 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_4_9)) ≤ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5639 (t x_0_3 x_3_4 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5640 (t x_0_5 x_0_6 x_1_3 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5642 (t x_0_4 x_1_4 x_1_6 x_4_5 x_4_6 x_4_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5645 (t x_0_4 x_3_4 x_4_5 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5646 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5648 (t x_0_1 x_1_2 x_2_3 x_3_4 x_4_5 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5650 (t x_4_6 x_6_8 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5654 (t x_0_1 x_1_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5657 (t x_0_1 x_1_7 x_6_7 x_7_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5658 (t x_0_1 x_1_7 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5659 (t x_1_4 x_3_4 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5660 (t x_1_3 x_1_4 x_3_4 x_3_9 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory5661 (t x_0_4 x_1_4 x_4_5 x_4_6 x_4_7 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5662 (t x_0_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5666 (t x_0_6 x_0_8 x_1_7 x_1_8 x_6_7 x_7_9 x_8_10 : ℝ) : (¬ (x_0_6 ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5667 (t x_0_8 x_1_7 x_1_8 x_6_7 x_7_8 x_7_9 x_8_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≤ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5668 (t x_0_4 x_1_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5672 (t x_0_5 x_2_3 x_3_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5673 (t x_0_1 x_1_3 x_1_4 x_3_4 x_4_5 : ℝ) : (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5674 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_6 : ℝ) : (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5676 (t x_0_4 x_2_3 x_3_4 x_4_5 x_4_6 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5677 (t x_0_1 x_1_2 x_1_4 x_3_4 x_4_5 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5678 (t x_0_2 x_1_4 x_2_3 x_2_4 x_3_4 x_4_5 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5682 (t x_0_1 x_1_3 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5684 (t x_1_3 x_2_3 x_3_4 x_3_9 x_4_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5689 (t x_0_1 x_1_2 x_1_8 x_1_9 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5691 (t x_0_1 x_1_2 x_1_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5692 (t x_0_1 x_1_3 x_1_7 x_3_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_1_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5693 (t x_0_2 x_2_3 x_3_6 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5695 (t x_0_5 x_5_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5698 (t x_0_1 x_1_2 x_1_6 x_3_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5699 (t x_3_4 x_3_7 x_4_5 : ℝ) : (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5702 (t x_0_4 x_1_4 x_4_5 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5703 (t x_0_1 x_0_4 x_1_4 x_4_7 x_4_8 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5706 (t x_0_3 x_3_4 x_3_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5707 (t x_0_1 x_1_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5709 (t x_0_3 x_3_4 x_3_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5710 (t x_0_3 x_2_3 x_3_4 x_3_8 x_4_8 x_8_9 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5711 (t x_0_3 x_1_3 x_2_3 x_3_4 x_3_8 x_4_8 x_8_9 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5713 (t x_0_1 x_1_2 x_1_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5714 (t x_0_1 x_1_4 x_2_4 x_4_5 x_4_7 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5716 (t x_0_1 x_1_7 x_3_5 x_3_7 x_5_6 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5717 (t x_0_5 x_3_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5718 (t x_0_1 x_1_5 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5719 (t x_0_1 x_1_3 x_2_3 x_3_4 x_3_5 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5720 (t x_0_1 x_1_3 x_2_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_3_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5721 (t x_0_1 x_1_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5723 (t x_0_3 x_1_2 x_2_3 x_3_4 x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5724 (t x_0_3 x_0_4 x_1_2 x_2_3 x_3_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_4_9 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5725 (t x_3_10 x_3_5 x_5_10 : ℝ) : (((((x_3_5 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_10)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_5_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_5_10) ≥ 1))) ↔ ((¬ ((¬ ((x_3_10 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_10)) ≤ 0)) ∨ (¬ ((t + x_3_5 + ((-1) * x_3_10)) ≥ 1)) ∨ (¬ ((t + x_3_10 + ((-1) * x_5_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_3_10 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_10)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_10) + x_5_10) ≥ 1)))))) := by
  classical
  have e0 : ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_10 + ((-1) * x_5_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_5) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_10) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_5 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_10 + ((-1) * x_5_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_5 + ((-1) * x_5_10)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_3_5 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_3_10 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory5727 (t x_0_2 x_2_4 x_3_4 x_4_5 x_4_9 : ℝ) : (¬ (x_4_9 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5728 (t x_0_4 x_3_4 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5729 (t x_0_3 x_3_5 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5730 (t x_0_2 x_2_3 x_3_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5732 (t x_0_3 x_0_4 x_3_4 x_4_5 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5733 (t x_0_4 x_2_4 x_4_5 x_4_8 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5734 (t x_0_1 x_1_2 x_1_6 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5735 (t x_0_4 x_3_5 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5736 (t x_0_3 x_0_5 x_0_8 x_3_4 x_4_6 x_4_8 x_5_6 x_8_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory5737 (t x_0_1 x_1_3 x_1_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5742 (t x_0_2 x_1_2 x_2_3 x_2_7 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ (x_2_7 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5744 (t x_0_5 x_2_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5746 (t x_0_1 x_1_3 x_1_5 x_3_4 x_3_5 x_4_6 x_5_8 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5748 (t x_0_1 x_1_3 x_3_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5749 (t x_0_4 x_1_2 x_2_4 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5750 (t x_0_4 x_2_3 x_3_4 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5752 (t x_0_7 x_3_5 x_5_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5754 (t x_0_3 x_1_3 x_3_4 x_3_9 x_9_10 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5755 (t x_0_3 x_1_3 x_3_4 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5756 (t x_0_1 x_1_4 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5759 (t x_0_1 x_1_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5760 (t x_1_2 x_2_3 x_2_5 x_3_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5762 (t x_0_4 x_1_3 x_3_4 x_3_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5763 (t x_0_3 x_1_3 x_3_4 x_3_7 x_4_7 x_7_8 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5764 (t x_1_5 x_4_5 x_5_6 x_5_9 x_6_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5766 (t x_0_1 x_1_2 x_1_3 x_2_3 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory5768 (t x_0_5 x_1_3 x_3_4 x_3_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5769 (t x_0_5 x_4_5 x_5_6 x_5_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5770 (t x_0_7 x_1_3 x_3_7 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5771 (t x_0_4 x_1_3 x_3_4 x_4_8 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ (x_9_10 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5774 (t x_0_4 x_0_5 x_1_3 x_3_4 x_4_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5776 (t x_0_4 x_1_3 x_3_4 x_4_5 x_5_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5777 (t x_0_4 x_1_3 x_3_4 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5780 (t x_0_5 x_4_5 x_5_7 x_5_9 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5782 (t x_0_3 x_1_3 x_3_5 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5785 (t x_0_1 x_1_5 x_5_7 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5788 (t x_0_1 x_1_5 x_3_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5789 (t x_2_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5791 (t x_0_4 x_1_2 x_2_4 x_4_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5792 (t x_0_2 x_1_3 x_2_3 x_2_7 x_3_4 x_3_7 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5793 (t x_0_3 x_1_3 x_3_5 x_3_7 x_7_8 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5794 (t x_0_3 x_1_3 x_1_4 x_2_3 x_3_4 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5795 (t x_2_4 x_4_5 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5796 (t x_0_4 x_2_4 x_4_7 x_4_8 x_7_9 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5798 (t x_0_1 x_1_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5799 (t x_0_3 x_1_3 x_3_5 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5801 (t x_0_2 x_2_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5802 (t x_0_3 x_2_7 x_3_4 x_3_7 x_7_9 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_2_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5804 (t x_0_1 x_1_5 x_3_4 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5805 (t x_0_3 x_2_3 x_3_5 x_3_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5806 (t x_2_6 x_5_6 x_6_7 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5808 (t x_0_3 x_3_4 x_3_6 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5810 (t x_1_3 x_3_4 x_3_6 x_6_7 x_7_9 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5811 (t x_1_3 x_2_6 x_3_4 x_3_6 x_6_8 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5812 (t x_2_3 x_3_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5813 (t x_0_3 x_2_3 x_3_5 x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5814 (t x_1_3 x_2_4 x_3_4 x_3_6 x_4_5 x_4_6 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5816 (t x_0_1 x_1_5 x_5_8 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_6_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5817 (t x_2_4 x_4_5 x_4_8 x_5_7 x_5_8 x_8_9 : ℝ) : ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5818 (t x_0_2 x_2_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5820 (t x_0_2 x_2_4 x_4_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5821 (t x_0_2 x_2_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5822 (t x_0_2 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5823 (t x_1_3 x_3_4 x_3_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5824 (t x_0_4 x_1_2 x_2_4 x_4_7 x_7_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5825 (t x_0_2 x_1_2 x_2_4 x_2_6 x_6_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5826 (t x_0_1 x_0_2 x_2_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5827 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_6 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_3_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5828 (t x_0_3 x_3_4 x_3_5 x_4_5 x_5_9 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5831 (t x_0_2 x_2_6 x_2_7 x_5_6 x_6_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory5833 (t x_0_2 x_1_3 x_2_6 x_2_8 x_3_4 x_3_6 : ℝ) : (t ≥ 4) ∨ (¬ (x_2_8 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5835 (t x_0_2 x_1_2 x_2_4 x_2_5 x_5_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5836 (t x_0_2 x_1_2 x_2_3 x_2_4 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_7)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5838 (t x_0_2 x_2_5 x_2_7 x_6_7 x_7_9 : ℝ) : (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5842 (t x_0_2 x_1_3 x_1_5 x_2_5 x_3_6 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5844 (t x_0_7 x_1_3 x_2_7 x_3_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5845 (t x_1_3 x_2_3 x_2_7 x_3_4 x_3_5 x_3_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5850 (t x_0_1 x_1_3 x_3_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5852 (t x_0_5 x_0_6 x_2_5 x_5_6 x_5_8 x_6_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ (x_2_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5853 (t x_1_2 x_2_4 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_6_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5854 (x_0_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory5855 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5858 (t x_0_1 x_0_5 x_1_5 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5859 (t x_0_6 x_0_7 x_3_6 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5860 (t x_0_3 x_1_3 x_2_3 x_3_4 x_3_6 x_6_9 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ (x_6_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5862 (t x_0_2 x_1_7 x_2_3 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5863 (t x_0_5 x_1_3 x_3_5 x_3_7 x_5_7 x_5_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5870 (t x_0_3 x_1_2 x_2_3 x_2_4 x_3_5 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5871 (t x_0_1 x_1_2 x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_1 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5872 (t x_0_3 x_0_7 x_1_3 x_3_4 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5873 (t x_1_3 x_3_5 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5875 (t x_0_3 x_1_3 x_3_4 x_3_6 x_4_5 x_5_6 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5876 (t x_4_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory5878 (t x_0_4 x_4_6 x_4_7 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5880 (x_3_6 x_4_6 x_5_6 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_5_6)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory5884 (x_0_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory5885 (t x_3_4 x_4_6 x_6_8 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory5886 (t x_0_6 x_1_6 x_3_4 x_4_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory5888 (t x_0_2 x_2_7 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5889 (t x_0_1 x_1_2 x_1_3 x_3_5 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory5892 (t x_0_7 x_1_3 x_3_4 x_3_7 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

end ElevenTheory
