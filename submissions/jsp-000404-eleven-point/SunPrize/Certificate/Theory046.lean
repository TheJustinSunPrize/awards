import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory15693 (t x_0_2 x_0_7 x_1_7 x_2_4 x_2_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_7) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15697 (t x_0_3 x_2_3 x_2_5 x_3_5 x_5_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15698 (t x_0_5 x_5_9 x_6_8 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ ((t + ((-1) * x_5_9)) ≤ 0) ∨ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory15700 (t x_0_7 x_1_6 x_1_7 x_2_6 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15701 (t x_0_6 x_0_7 x_6_7 x_6_8 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15702 (t x_0_1 x_0_4 x_1_2 x_2_5 x_4_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15705 (t x_0_2 x_2_3 x_2_4 x_4_5 x_5_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ (x_5_9 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15707 (t x_0_3 x_0_8 x_0_9 x_2_3 x_3_9 x_9_10 : ℝ) : (¬ ((x_0_8 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15709 (x_3_5 x_3_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory15710 (t x_0_2 x_2_5 x_2_8 x_3_8 x_5_6 x_5_8 : ℝ) : (¬ ((x_2_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15714 (t x_0_3 x_0_5 x_2_3 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15715 (t x_0_3 x_1_2 x_2_3 x_2_6 x_3_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15716 (t x_0_5 x_1_2 x_2_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory15717 (t x_0_3 x_3_4 x_3_5 x_4_5 x_4_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15721 (t x_0_1 x_0_2 x_1_3 x_2_5 x_3_7 x_5_9 x_7_10 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + x_7_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory15722 (t x_0_1 x_0_8 x_1_3 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15723 (t x_0_3 x_1_7 x_2_3 x_2_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15728 (x_1_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15733 (t x_0_3 x_0_6 x_2_3 x_3_4 x_3_6 x_6_8 : ℝ) : (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15735 (t x_0_4 x_3_4 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15736 (t x_0_3 x_0_6 x_2_3 x_3_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15737 (x_2_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_2_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15742 (t x_0_5 x_4_6 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15745 (x_1_6 x_2_6 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15755 (x_0_2 x_1_2 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15756 (t x_0_1 x_0_2 x_1_3 x_2_6 x_3_7 x_6_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory15757 (x_4_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15758 (t x_0_9 x_3_6 x_5_7 x_6_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_5_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_6_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15760 (x_1_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15761 (t x_0_3 x_1_2 x_2_3 x_2_5 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15762 (t x_0_5 x_1_6 x_2_6 x_5_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15763 (t x_1_5 x_4_7 x_5_7 x_5_9 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15764 (t x_1_5 x_1_6 x_4_5 x_5_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15767 (t x_0_3 x_0_4 x_2_3 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15775 (x_1_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15778 (t x_1_7 x_2_7 x_6_7 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_2_7) + x_6_7) ≥ 1)) ∨ ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15779 (t x_1_7 x_5_7 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ ((t + x_1_7 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15780 (t x_0_3 x_1_3 x_2_3 x_2_5 x_3_5 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15783 (x_3_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15784 (t x_2_6 x_2_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15785 (t x_0_5 x_2_5 x_5_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15786 (t x_0_3 x_1_3 x_2_3 x_3_4 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15790 (t x_0_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15792 (t x_0_2 x_1_2 x_2_4 x_2_5 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15793 (t x_0_4 x_3_4 x_4_5 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15794 (x_0_4 x_0_5 x_0_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_0_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15795 (t x_0_3 x_0_8 x_2_3 x_3_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15796 (t x_0_7 x_0_8 x_5_7 x_7_8 x_8_9 : ℝ) : (¬ ((t + x_0_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15797 (t x_0_3 x_1_5 x_3_5 x_3_6 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15799 (t x_0_1 x_1_6 x_4_5 x_4_6 x_5_8 x_6_7 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15802 (x_0_1 x_0_4 x_0_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ ((x_0_1 + ((-1) * x_0_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15805 (x_0_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15811 (x_0_3 x_0_4 x_0_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ ((x_0_3 + ((-1) * x_0_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15816 (t x_0_1 x_1_2 x_2_5 x_5_6 x_6_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15820 (t x_0_1 x_0_4 x_1_3 x_3_6 x_4_5 x_5_6 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory15825 (t x_0_3 x_2_3 x_2_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15826 (t x_0_2 x_1_2 x_2_4 x_2_6 x_4_5 x_4_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((t + x_4_5 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15831 (t x_3_5 x_4_5 x_5_7 x_5_8 x_8_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_8_10 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15834 (x_1_3 x_1_4 x_1_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_1_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15835 (t x_3_6 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory15840 (t x_0_7 x_1_4 x_4_7 x_4_9 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15841 (x_0_8 x_4_8 x_8_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≤ 0)) ∨ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15842 (t x_0_4 x_0_5 x_1_4 x_4_5 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15848 (x_0_7 x_1_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory15849 (x_1_9 x_2_9 x_9_10 : ℝ) : (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_2_9)) ≥ 0)) ∨ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15855 (t x_0_5 x_0_6 x_5_6 x_5_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_7) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15858 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_6 x_6_9 x_7_10 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_7_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory15859 (t x_0_1 x_1_2 x_1_5 x_1_6 x_2_5 x_2_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((t + x_2_5 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15861 (t x_0_2 x_1_2 x_1_3 x_2_3 x_3_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15862 (t x_0_1 x_1_3 x_1_6 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_4_6)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15863 (t x_2_3 x_3_5 x_5_7 x_7_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15866 (t x_0_4 x_0_6 x_3_4 x_4_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15871 (t x_0_3 x_3_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15885 (t x_1_4 x_4_5 x_4_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15886 (x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15887 (t x_0_2 x_0_6 x_2_6 x_6_8 x_6_9 x_9_10 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15890 (t x_1_7 x_1_9 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_1_9)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15893 (t x_3_5 x_5_6 x_5_8 x_6_7 x_6_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15895 (t x_0_5 x_1_5 x_4_5 x_5_6 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15898 (t x_1_3 x_2_3 x_3_5 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15899 (t x_3_9 x_4_7 x_5_8 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_3_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15900 (t x_0_1 x_0_2 x_0_3 x_2_4 x_3_8 x_4_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_2)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory15903 (x_2_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_6_7)) ≤ 0)) ∨ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15909 (x_0_9 x_1_9 x_4_9 : ℝ) : (¬ ((x_0_9 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_4_9)) ≥ 0)) ∨ ((x_0_9 + ((-1) * x_4_9)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15910 (t x_0_5 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15912 (t x_3_4 x_4_7 x_6_7 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory15913 (t x_0_1 x_1_5 x_1_8 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15915 (t x_0_1 x_1_3 x_1_4 x_4_7 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ (x_7_8 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15917 (t x_0_3 x_0_4 x_2_3 x_3_4 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15918 (t x_0_1 x_0_3 x_1_6 x_1_7 x_3_5 x_5_8 x_7_8 x_8_10 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory15919 (t x_0_3 x_0_7 x_2_3 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15920 (x_1_3 x_2_3 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15921 (t x_0_2 x_1_2 x_1_3 x_2_3 x_2_4 x_2_6 x_3_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory15922 (x_0_1 x_0_2 x_1_3 x_1_6 x_2_3 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory15923 (t x_0_8 x_3_4 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15925 (t x_2_6 x_3_5 x_4_5 x_4_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15926 (t x_0_4 x_3_4 x_4_5 x_4_7 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15931 (t x_0_4 x_4_5 x_4_7 x_5_6 x_5_7 : ℝ) : (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15932 (x_0_5 x_4_5 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15935 (t x_0_3 x_3_4 x_4_5 x_5_9 x_9_10 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15938 (t x_0_3 x_0_5 x_0_8 x_2_3 x_3_5 x_3_6 x_5_8 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory15939 (t x_0_3 x_2_3 x_2_7 x_3_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15941 (x_0_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15942 (t x_0_3 x_0_4 x_1_4 x_3_4 x_3_5 x_4_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15945 (t x_0_3 x_0_5 x_2_3 x_2_6 x_3_5 x_3_6 x_5_8 x_6_8 x_8_10 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory15947 (t x_0_3 x_0_4 x_2_3 x_3_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15950 (t x_0_3 x_2_3 x_3_5 x_3_6 x_3_7 x_5_7 x_6_8 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory15952 (t x_0_7 x_2_4 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15955 (t x_0_3 x_3_4 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15957 (t x_1_5 x_3_4 x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15958 (t x_0_4 x_0_5 x_4_5 x_4_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((t + x_4_5 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15964 (x_0_4 x_3_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15965 (x_0_4 x_3_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15966 (t x_0_3 x_0_5 x_2_3 x_3_5 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory15974 (t x_1_5 x_3_5 x_4_5 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15976 (t x_4_5 x_4_6 x_4_7 : ℝ) : (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ ((t + ((-1) * x_4_6) + x_4_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15977 (t x_0_2 x_0_4 x_2_3 x_3_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15986 (t x_0_6 x_3_6 x_5_6 x_6_7 x_6_8 : ℝ) : ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15987 (x_2_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15991 (t x_0_4 x_0_7 x_4_5 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15992 (t x_0_4 x_1_4 x_3_4 x_4_5 x_4_7 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_4_8 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory15994 (t x_3_4 x_4_5 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory15996 (t x_1_8 x_6_8 x_7_8 : ℝ) : (¬ ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) ∨ ((t + x_1_8 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory15997 (t x_0_4 x_1_2 x_1_4 x_2_3 x_3_4 x_4_5 x_4_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16000 (x_0_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16004 (t x_0_2 x_2_4 x_2_5 x_4_5 x_4_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16007 (t x_0_7 x_4_8 x_5_7 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16008 (x_0_1 x_0_2 x_1_5 x_2_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory16010 (t x_0_3 x_0_4 x_2_3 x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16011 (t x_0_3 x_0_7 x_1_2 x_1_3 x_1_7 x_3_4 x_4_6 x_5_7 x_6_9 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_7) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory16012 (t x_0_9 x_5_8 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_0_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16016 (t x_3_4 x_4_5 x_4_7 x_4_9 x_6_9 x_9_10 : ℝ) : ((t + ((-1) * x_6_9)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16021 (t x_0_1 x_0_2 x_0_6 x_1_2 x_2_4 x_4_10 x_4_9 x_6_9 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + x_4_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_6) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16022 (x_0_3 x_1_3 x_3_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16028 (x_0_3 x_1_3 x_3_5 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory16029 (t x_2_3 x_2_5 x_3_4 x_3_5 x_3_6 x_5_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_6) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16031 (t x_1_2 x_2_3 x_2_7 x_3_4 x_3_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16034 (x_0_8 x_2_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16035 (t x_0_2 x_0_4 x_1_2 x_1_3 x_2_3 x_2_4 x_3_8 x_4_9 x_5_8 x_8_10 x_9_10 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory16040 (t x_0_1 x_0_2 x_0_3 x_1_3 x_2_6 x_3_5 x_3_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16041 (x_1_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16042 (x_1_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16045 (t x_0_4 x_1_2 x_2_4 x_4_6 x_4_8 : ℝ) : (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16048 (t x_0_4 x_0_7 x_2_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16051 (t x_0_5 x_2_5 x_5_7 x_5_9 x_7_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16052 (t x_0_1 x_1_2 x_1_6 x_2_6 x_6_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16053 (t x_0_7 x_1_6 x_4_5 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16055 (t x_0_3 x_0_5 x_1_3 x_3_4 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16058 (x_3_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16061 (t x_1_2 x_2_4 x_2_6 x_4_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16062 (t x_1_2 x_2_4 x_2_6 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16064 (t x_0_6 x_1_4 x_1_5 x_1_6 x_3_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16065 (t x_0_5 x_2_6 x_5_6 x_6_10 x_6_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16066 (t x_0_2 x_0_3 x_0_4 x_3_6 x_4_5 x_5_8 x_6_9 x_8_10 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16067 (t x_0_5 x_4_5 x_4_6 x_5_6 x_5_8 x_6_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16069 (t x_0_4 x_4_6 x_4_7 x_6_7 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16070 (x_3_9 x_4_10 x_4_9 x_9_10 : ℝ) : (¬ ((x_4_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_4_10)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory16071 (t x_0_2 x_0_3 x_1_2 x_2_3 x_2_4 x_3_6 x_4_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16072 (t x_1_2 x_1_4 x_2_3 x_2_4 x_4_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16073 (t x_0_4 x_0_6 x_3_4 x_4_5 x_4_6 x_4_7 x_6_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16074 (t x_0_2 x_1_2 x_2_3 x_2_4 x_2_8 : ℝ) : ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16078 (x_0_5 x_1_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory16081 (t x_0_5 x_1_5 x_4_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16084 (t x_0_1 x_0_4 x_1_6 x_3_4 x_4_5 x_4_8 x_5_6 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16085 (t x_3_5 x_4_5 x_5_6 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16091 (t x_0_3 x_0_7 x_0_9 x_2_3 x_2_4 x_3_4 x_3_7 x_4_6 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory16103 (t x_0_3 x_2_3 x_3_4 x_3_7 x_4_9 x_6_7 x_7_10 x_7_9 x_9_10 : ℝ) : ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16106 (t x_0_2 x_0_4 x_1_2 x_1_4 x_2_3 x_3_7 x_4_6 x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_7_8) + x_7_9) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16108 (x_0_4 x_1_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16109 (t x_0_5 x_1_5 x_4_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_5) + x_4_5) ≥ 1)) ∨ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16116 (t x_0_2 x_0_4 x_1_2 x_2_3 x_3_4 x_4_7 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16117 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_5 x_3_4 x_4_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_9) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16118 (t x_3_4 x_4_6 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_6)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16121 (t x_0_2 x_0_3 x_0_6 x_2_6 x_3_5 x_5_8 x_6_7 x_6_9 x_8_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16122 (t x_0_2 x_0_3 x_0_6 x_2_6 x_3_4 x_4_8 x_6_7 x_6_9 x_8_9 : ℝ) : (¬ ((t + x_6_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16125 (t x_0_2 x_0_3 x_2_3 x_2_4 x_2_9 x_3_5 x_4_9 x_5_8 x_8_10 x_9_10 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16126 (t x_0_2 x_0_3 x_2_3 x_2_4 x_2_9 x_3_7 x_4_9 x_7_8 x_8_10 x_9_10 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16128 (t x_0_2 x_0_4 x_2_5 x_3_4 x_4_7 x_4_9 x_5_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_2) + x_0_4) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16129 (t x_0_2 x_0_3 x_0_4 x_0_5 x_2_5 x_3_7 x_3_9 x_4_6 x_4_7 x_5_8 x_5_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((t + x_5_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  linarith

theorem theory16130 (t x_0_8 x_2_6 x_2_8 x_6_7 x_6_8 x_8_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16131 (t x_0_1 x_0_2 x_0_4 x_2_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16132 (t x_0_8 x_2_6 x_2_8 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((t + x_2_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16135 (t x_0_4 x_3_4 x_4_7 x_4_8 x_7_10 x_7_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_7_8) + x_7_10) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16137 (t x_0_6 x_2_6 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16138 (x_0_1 x_1_6 x_1_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16139 (t x_0_4 x_3_4 x_4_5 x_4_6 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16140 (t x_0_1 x_0_2 x_1_4 x_2_8 x_4_5 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_2) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((t + x_5_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16141 (t x_1_5 x_2_5 x_4_5 x_5_6 x_5_7 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16145 (t x_0_2 x_0_3 x_2_5 x_3_7 x_5_8 x_7_8 x_8_10 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory16146 (x_3_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16148 (t x_1_6 x_4_6 x_5_6 : ℝ) : (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16149 (t x_0_2 x_0_4 x_1_2 x_1_3 x_2_3 x_2_4 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory16151 (t x_0_2 x_1_2 x_2_5 x_2_7 x_5_6 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16152 (t x_0_5 x_1_5 x_5_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory16154 (t x_0_4 x_0_6 x_1_2 x_1_4 x_1_6 x_3_6 x_4_5 x_4_8 x_5_8 x_6_7 x_6_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory16156 (t x_0_1 x_0_2 x_1_2 x_1_3 x_1_6 x_2_4 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory16157 (t x_0_5 x_3_4 x_4_5 x_4_6 x_5_6 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory16159 (t x_2_6 x_4_6 x_4_8 x_6_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_2_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory16160 (x_0_3 x_3_4 x_3_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((x_0_3 + ((-1) * x_3_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory16163 (t x_0_1 x_0_3 x_0_4 x_1_2 x_1_3 x_1_6 x_3_4 x_4_5 x_4_8 x_6_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + x_4_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

end ElevenTheory
