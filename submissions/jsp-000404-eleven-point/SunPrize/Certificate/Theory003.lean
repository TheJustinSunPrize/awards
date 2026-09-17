import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory715 (x_0_1 x_1_4 x_1_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory716 (x_0_1 x_1_4 x_1_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ ((x_0_1 + ((-1) * x_1_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory717 (x_2_7 x_3_7 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory718 (x_2_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory719 (x_0_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory720 (x_0_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_0_3 + ((-1) * x_3_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory721 (x_1_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory722 (x_0_3 x_1_3 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory725 (x_2_6 x_3_6 x_6_10 : ℝ) : (¬ ((x_2_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory727 (x_0_6 x_2_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory728 (x_1_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory731 (x_0_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory732 (x_3_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory734 (x_3_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory735 (x_3_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory736 (x_0_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory737 (x_1_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory739 (x_0_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory741 (x_2_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory742 (x_6_8 x_7_8 : ℝ) : ((x_6_8 + ((-1) * x_7_8)) ≥ 0) ∨ ((x_6_8 + ((-1) * x_7_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory743 (x_2_6 x_3_6 : ℝ) : ((x_2_6 + ((-1) * x_3_6)) ≥ 0) ∨ ((x_2_6 + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory744 (x_2_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory745 (x_0_1 x_1_5 x_1_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory746 (t x_2_10 : ℝ) : ((¬ (t ≤ x_2_10)) ↔ (¬ ((t + ((-1) * x_2_10)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_10) ↔ (((1) * t + (-1) * x_2_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_10)) ≤ 0) ↔ (((1) * t + (-1) * x_2_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory748 (x_0_8 x_2_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory749 (x_0_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory750 (x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory753 (x_0_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory755 (x_2_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory756 (x_0_4 x_2_4 x_4_9 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory757 (x_2_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory758 (x_3_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory760 (x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory761 (x_2_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory763 (x_0_5 x_3_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_3_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory764 (x_6_7 x_6_8 x_6_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≤ 0)) ∨ ((x_6_7 + ((-1) * x_6_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory765 (x_2_7 x_5_7 x_7_10 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_2_7 + ((-1) * x_7_10)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory766 (x_3_8 x_4_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory767 (x_0_5 x_1_5 x_2_5 : ℝ) : (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ ((x_0_5 + ((-1) * x_1_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory768 (x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_5_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory769 (x_4_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory770 (x_0_8 x_2_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory771 (x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory772 (x_1_5 x_2_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory773 (x_2_5 x_3_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory774 (x_2_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory776 (x_0_3 x_3_8 x_3_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory779 (x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory780 (x_1_8 x_1_9 x_2_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_2_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory782 (x_0_2 x_2_4 x_2_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory783 (x_1_5 x_2_5 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory784 (x_3_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory786 (x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory787 (x_3_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory788 (x_0_4 x_1_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory789 (x_0_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory791 (x_1_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory793 (x_0_4 x_1_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory794 (x_0_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory795 (x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory796 (x_1_6 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory797 (x_0_2 x_2_3 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory799 (x_1_2 x_1_4 x_1_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ ((x_1_2 + ((-1) * x_1_7)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory802 (x_1_3 x_2_3 x_3_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory803 (x_0_2 x_2_5 x_2_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory804 (x_1_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory806 (x_0_5 x_2_5 x_5_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory807 (t x_3_7 x_5_7 x_6_7 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_7) + x_6_7) ≥ 1)) ∨ ((t + ((-1) * x_3_7) + x_5_7) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory808 (x_4_5 x_4_7 x_5_8 x_7_8 : ℝ) : (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory809 (x_0_5 x_1_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory810 (x_0_2 x_2_3 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_8)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory814 (x_3_8 x_4_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory815 (x_0_8 x_4_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory817 (x_1_3 x_3_8 x_3_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory818 (x_0_1 x_1_3 x_1_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory822 (x_1_8 x_4_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((x_4_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory823 (x_2_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_3_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory828 (x_0_5 x_1_5 x_2_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory829 (x_1_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_1_4 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory830 (x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory832 (x_1_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory833 (x_0_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory834 (x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory835 (x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory836 (x_1_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory837 (x_0_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory839 (x_0_5 x_3_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory840 (x_0_5 x_2_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory841 (x_0_2 x_2_4 x_2_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≥ 0)) ∨ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory842 (x_3_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory843 (x_0_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory846 (x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory848 (x_1_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory849 (x_0_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory850 (x_3_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((x_3_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory851 (t x_1_2 x_1_4 x_1_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory853 (x_0_4 x_1_4 x_2_4 x_3_4 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_3_4)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory854 (x_0_4 x_1_4 x_2_4 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_1_4)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory856 (x_0_4 x_1_4 x_2_4 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_1_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory858 (x_1_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory859 (x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_2_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory860 (x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory861 (x_0_7 x_5_7 x_7_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory863 (x_0_4 x_3_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory864 (x_5_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory865 (x_2_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory866 (x_1_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory867 (x_0_4 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory869 (x_0_5 x_2_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory870 (x_0_5 x_2_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((x_0_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory871 (t x_4_8 x_6_8 x_7_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory872 (x_0_4 x_3_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory873 (x_3_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory874 (x_0_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory875 (x_0_5 x_2_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory876 (x_1_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory877 (x_3_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory878 (x_0_2 x_2_5 x_2_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory879 (x_0_3 x_3_5 x_3_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory880 (x_2_6 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory882 (x_0_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_0_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory883 (x_1_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory884 (x_1_5 x_2_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory886 (x_1_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory887 (x_3_6 x_4_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory889 (x_2_3 x_3_6 x_3_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory890 (x_0_4 x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory891 (x_2_3 x_3_5 x_3_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory892 (x_3_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory894 (x_0_7 x_3_7 x_7_10 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory895 (x_2_3 x_2_5 x_3_4 x_3_5 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory896 (x_2_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory897 (x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory898 (x_5_6 x_6_10 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_6_10)) ≥ 0)) ∨ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory899 (x_0_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory900 (x_0_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory901 (t x_5_9 x_6_9 x_7_9 : ℝ) : (¬ ((t + x_5_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≤ 0)) ∨ ((t + x_5_9 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory902 (x_1_2 x_2_3 x_2_5 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory905 (x_3_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) ∨ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory907 (x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory909 (x_0_4 x_0_5 x_0_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_0_8)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory910 (x_0_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory913 (x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory914 (x_1_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_1_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory915 (t x_0_6 x_2_6 x_5_6 : ℝ) : (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_2_6) + x_5_6) ≥ 1)) ∨ ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory916 (x_3_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory918 (x_1_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory921 (x_2_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory922 (x_2_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory923 (x_3_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory924 (x_4_6 x_4_7 x_4_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_4_6 + ((-1) * x_4_8)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory926 (x_0_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory927 (t x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory928 (x_2_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory930 (x_4_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory932 (x_3_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory936 (x_1_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory937 (x_0_1 x_1_4 x_1_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory938 (x_2_3 x_3_5 x_3_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory939 (x_1_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory940 (x_2_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory941 (x_0_5 x_1_5 x_4_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((x_0_5 + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory942 (x_3_4 x_3_5 x_3_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_3_4 + ((-1) * x_3_8)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory944 (x_1_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory945 (x_1_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory946 (x_0_5 x_1_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ ((x_0_5 + ((-1) * x_5_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory948 (x_1_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory950 (x_2_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory951 (x_3_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((x_3_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory952 (x_0_6 x_4_6 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory954 (x_0_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory956 (x_2_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory957 (x_0_3 x_3_5 x_3_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory960 (x_1_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory961 (x_1_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≤ 0)) ∨ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory962 (x_0_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_3_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory963 (x_0_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory965 (x_0_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory966 (x_3_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) ∨ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory968 (t x_4_8 x_6_8 x_7_8 : ℝ) : (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ ((t + x_4_8 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory972 (x_3_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory974 (x_0_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory975 (x_3_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory976 (x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory977 (x_2_4 x_3_4 x_4_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory978 (x_0_2 x_2_4 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory979 (x_0_5 x_5_6 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_9)) ≤ 0)) ∨ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory980 (x_4_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≤ 0)) ∨ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory981 (x_2_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory982 (x_1_2 x_2_3 x_2_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) ∨ ((x_1_2 + ((-1) * x_2_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory984 (x_0_1 x_1_2 x_1_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory985 (x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ ((x_6_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory986 (x_0_4 x_3_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory987 (x_1_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory988 (x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory989 (x_2_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ ((x_2_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory990 (x_2_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) ∨ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory991 (x_2_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory992 (x_0_6 x_4_6 : ℝ) : ((x_0_6 + ((-1) * x_4_6)) ≤ 0) ∨ ((x_0_6 + ((-1) * x_4_6)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory993 (x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

end ElevenTheory
