import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory2002 (t x_0_4 x_0_5 x_1_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2005 (t x_0_2 x_1_4 x_2_4 x_2_7 x_4_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2007 (t x_0_8 x_1_4 x_2_3 x_3_4 x_3_8 x_4_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2009 (t x_0_7 x_1_4 x_2_4 x_2_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2011 (t x_0_1 x_0_4 x_1_6 x_4_5 x_4_7 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2013 (t x_0_6 x_1_6 x_5_6 x_6_7 x_6_8 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_6_8 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2017 (t x_0_5 x_1_3 x_2_4 x_3_4 x_3_5 x_4_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2019 (t x_0_1 x_0_4 x_1_7 x_3_7 x_4_5 x_5_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2021 (t x_3_10 x_3_6 x_6_10 : ℝ) : ((((x_3_6 ≤ x_3_10) ∧ (x_3_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_3_6 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_3_6 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_3_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_6 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_6 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_3_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_6 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_6_10) ↔ (((1) * x_3_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_3_10 ≤ x_3_6) ↔ (((1) * x_3_10 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_10 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_6 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_6) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory2022 (t x_3_6 x_3_7 x_5_7 x_6_10 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_10) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2026 (t x_0_1 x_0_4 x_1_3 x_3_7 x_4_5 x_5_6 x_5_7 x_6_9 x_7_10 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_7_9) + x_7_10) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory2028 (x_1_2 x_2_5 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory2031 (t x_0_2 x_0_3 x_2_3 x_2_7 x_2_9 x_3_5 x_5_6 x_6_10 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory2036 (t x_0_1 x_0_4 x_1_7 x_2_7 x_3_4 x_4_5 x_4_7 x_7_8 : ℝ) : (¬ ((t + x_2_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2040 (t x_1_2 x_1_7 x_2_3 x_2_4 x_2_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2041 (t x_0_3 x_1_2 x_1_3 x_2_3 x_2_4 x_3_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2046 (t x_0_3 x_1_5 x_3_5 x_3_8 x_5_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2052 (t x_0_1 x_0_5 x_1_4 x_4_6 x_5_7 x_6_10 x_7_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_5)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2053 (t x_0_5 x_1_3 x_3_5 x_3_8 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2054 (x_7_9 x_9_10 : ℝ) : (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2057 (t x_0_5 x_1_3 x_3_5 x_3_6 x_5_6 : ℝ) : (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2058 (t x_0_4 x_0_5 x_3_4 x_4_5 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2060 (t x_0_4 x_2_3 x_3_4 x_3_7 x_4_7 : ℝ) : (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2062 (t x_0_4 x_1_4 x_3_4 x_4_6 x_4_8 x_6_7 x_6_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2064 (t x_0_4 x_1_4 x_1_5 x_4_5 x_5_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2065 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_4 x_4_5 x_5_8 x_7_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory2066 (t x_0_1 x_1_2 x_1_3 x_2_3 x_2_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2067 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_6 x_6_8 x_7_9 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory2068 (t x_0_1 x_1_3 x_1_8 x_2_3 x_3_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2069 (x_1_7 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2070 (t x_0_1 x_0_8 x_1_2 x_1_8 x_8_10 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_8) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2071 (t x_1_5 x_1_7 x_5_6 x_5_7 x_7_10 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2072 (t x_1_4 x_1_6 x_3_4 x_4_6 x_6_8 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2073 (t x_0_1 x_0_8 x_1_2 x_1_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_8) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2074 (t x_0_1 x_0_3 x_0_4 x_1_2 x_1_3 x_1_7 x_3_4 x_4_6 x_4_8 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory2075 (t x_0_5 x_0_7 x_1_4 x_1_5 x_3_4 x_4_7 x_5_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2077 (t x_0_1 x_1_4 x_1_7 x_3_4 x_4_7 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2078 (t x_4_6 x_5_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2080 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_5 x_5_6 x_6_9 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory2081 (t x_3_6 x_4_6 x_5_6 x_6_7 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2082 (x_0_1 x_1_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2083 (t x_0_4 x_3_6 x_4_6 x_4_8 x_6_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2084 (t x_1_6 x_1_9 x_3_6 x_4_6 x_6_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2085 (t x_0_4 x_1_7 x_2_4 x_2_7 x_4_7 x_7_8 : ℝ) : (¬ ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2086 (t x_0_7 x_1_4 x_3_5 x_4_5 x_4_7 x_5_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2088 (t x_0_7 x_1_4 x_1_7 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2090 (t x_0_4 x_4_7 x_4_9 x_5_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2092 (t x_3_6 x_4_5 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2093 (t x_0_4 x_0_6 x_4_6 x_4_8 x_6_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_6) + x_4_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2094 (t x_0_3 x_1_3 x_1_7 x_3_5 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_7) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2095 (t x_2_4 x_2_6 x_4_5 x_4_6 x_4_8 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_8) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2096 (t x_0_3 x_0_6 x_3_4 x_3_6 x_3_7 x_6_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2097 (t x_0_4 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2098 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_4 x_4_6 x_6_9 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory2099 (t x_0_1 x_1_2 x_1_4 x_1_7 x_4_9 x_5_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory2100 (t x_0_4 x_2_3 x_3_4 x_3_6 x_4_6 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2101 (t x_2_10 x_2_7 x_7_10 : ℝ) : ((((x_2_7 ≤ x_2_10) ∧ (x_2_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_2_7 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_2_7 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((x_2_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_2_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_7 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_7 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_7 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_7_10) ↔ (((1) * x_2_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_10 ≤ x_2_7) ↔ (((1) * x_2_10 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_7 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_7) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory2103 (t x_0_5 x_4_5 x_4_9 x_5_9 x_9_10 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2104 (t x_0_1 x_1_2 x_1_7 x_2_4 x_2_7 : ℝ) : (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2106 (t x_1_9 x_7_8 x_8_10 x_8_9 x_9_10 : ℝ) : (¬ ((t + x_1_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_8_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2108 (t x_1_5 x_1_9 x_3_5 x_5_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2109 (t x_0_1 x_1_2 x_1_3 x_1_8 x_3_6 x_6_9 x_8_10 x_9_10 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2111 (t x_0_1 x_1_2 x_1_6 x_1_7 x_5_6 x_6_8 x_6_9 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_7_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_6) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2112 (t x_0_2 x_2_3 x_2_7 x_3_4 x_3_7 : ℝ) : (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2113 (t x_0_5 x_0_6 x_0_8 x_3_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2114 (t x_1_6 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2116 (t x_0_5 x_0_8 x_4_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2117 (t x_1_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2118 (t x_0_3 x_3_6 x_3_8 x_4_6 x_6_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2119 (t x_0_3 x_1_6 x_3_6 x_3_7 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_6) + x_3_6) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2120 (t x_0_5 x_1_3 x_2_3 x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2121 (t x_0_5 x_2_5 x_4_6 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2122 (t x_0_3 x_1_3 x_2_5 x_3_5 x_3_7 x_5_7 : ℝ) : (¬ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2124 (t x_0_8 x_2_5 x_4_6 x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2126 (t x_1_3 x_3_4 x_3_5 x_4_5 x_4_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2127 (t x_0_4 x_0_6 x_2_3 x_2_6 x_3_4 x_3_5 x_6_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2129 (t x_2_5 x_3_6 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2130 (t x_0_6 x_2_5 x_3_5 x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2132 (t x_1_2 x_1_4 x_2_3 x_2_4 x_2_5 x_4_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2133 (t x_1_3 x_2_5 x_3_5 x_3_7 x_5_7 : ℝ) : (¬ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2134 (t x_1_2 x_2_4 x_2_5 x_4_5 x_4_9 : ℝ) : (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2135 (t x_1_2 x_2_4 x_2_6 x_4_6 x_4_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_6) + x_4_8) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2136 (t x_0_5 x_1_6 x_5_6 x_5_7 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_1_6) + x_5_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2137 (t x_0_7 x_1_3 x_3_7 x_3_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2138 (t x_0_3 x_1_3 x_2_3 x_2_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2141 (t x_1_3 x_3_4 x_3_9 x_4_5 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2142 (t x_3_4 x_3_9 x_4_5 x_4_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2143 (t x_0_1 x_0_6 x_1_3 x_3_9 x_6_7 x_7_8 x_8_10 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2144 (t x_0_4 x_4_6 x_4_9 x_5_6 x_6_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2145 (t x_1_6 x_3_4 x_4_6 x_4_9 x_6_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2147 (t x_1_6 x_3_4 x_3_6 x_4_5 x_4_6 x_6_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2149 (x_5_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2150 (t x_0_6 x_1_4 x_1_6 x_4_5 x_4_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2151 (t x_1_4 x_1_9 x_3_9 x_4_5 x_4_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2152 (t x_1_4 x_1_6 x_3_4 x_4_5 x_4_6 x_6_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2155 (x_1_4 x_4_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2158 (x_1_2 x_2_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2159 (x_0_2 x_0_5 x_2_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory2160 (t x_3_6 x_6_7 x_6_8 x_7_10 x_7_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_7_8) + x_7_10) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2161 (t x_0_8 x_1_5 x_1_8 x_3_5 x_5_8 x_8_9 : ℝ) : (¬ ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2162 (t x_0_1 x_0_2 x_1_2 x_1_3 x_2_5 : ℝ) : (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2163 (t x_0_2 x_0_3 x_2_5 x_3_4 x_4_7 x_5_7 x_7_8 x_7_9 : ℝ) : (¬ ((t + ((-1) * x_0_2) + x_0_3) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2166 (t x_3_6 x_5_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2167 (t x_4_8 x_4_9 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_8) + x_5_8) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2168 (t x_0_1 x_1_5 x_1_8 x_2_5 x_5_8 : ℝ) : (¬ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2169 (t x_0_2 x_0_3 x_0_5 x_1_2 x_1_3 x_3_4 x_4_7 x_5_8 x_7_10 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((t + ((-1) * x_7_10) + x_9_10) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory2170 (x_2_5 x_5_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2171 (t x_1_3 x_2_3 x_2_4 x_3_4 x_4_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2172 (t x_1_6 x_1_8 x_6_10 x_6_7 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_10) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2174 (t x_1_4 x_4_6 x_4_7 x_5_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2176 (x_0_2 x_0_3 x_0_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_0_5)) ≥ 0) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory2177 (t x_0_1 x_1_3 x_1_6 x_2_3 x_3_6 : ℝ) : (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2179 (x_6_9 x_9_10 : ℝ) : (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2181 (t x_1_4 x_1_6 x_4_5 x_4_6 x_6_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2183 (t x_0_4 x_0_7 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2184 (t x_0_4 x_4_7 x_4_8 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2185 (t x_0_3 x_3_6 x_3_8 x_6_7 x_6_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2186 (t x_0_4 x_0_5 x_1_5 x_4_5 x_4_6 x_5_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2188 (t x_0_4 x_3_6 x_4_6 x_4_7 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2189 (t x_1_4 x_1_7 x_3_4 x_4_7 x_7_9 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2190 (t x_0_1 x_1_4 x_1_6 x_4_5 x_4_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2191 (t x_0_4 x_0_5 x_4_5 x_4_9 x_5_6 : ℝ) : (¬ ((t + ((-1) * x_4_5) + x_4_9) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2192 (t x_0_1 x_1_4 x_1_8 x_3_4 x_4_5 x_4_8 : ℝ) : (¬ ((x_1_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2194 (t x_0_1 x_0_5 x_1_2 x_1_5 x_5_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2195 (t x_0_4 x_4_8 x_4_9 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_8) + x_5_8) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2196 (t x_5_8 x_6_7 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2197 (t x_3_7 x_3_8 x_4_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2198 (t x_3_8 x_4_7 x_6_7 x_6_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2199 (t x_2_3 x_2_7 x_3_4 x_3_7 x_7_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2200 (t x_1_3 x_3_7 x_3_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2201 (t x_0_7 x_2_5 x_4_5 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2202 (t x_4_7 x_5_6 x_6_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2203 (t x_0_6 x_0_8 x_6_7 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2204 (t x_0_8 x_4_6 x_4_8 x_6_7 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2205 (t x_0_1 x_1_4 x_1_7 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2206 (t x_1_3 x_1_4 x_3_4 x_3_5 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2207 (t x_0_4 x_3_5 x_4_5 x_4_6 x_5_6 : ℝ) : (¬ ((t + x_3_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2208 (t x_0_1 x_1_2 x_1_3 x_2_3 x_2_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_6) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2209 (t x_0_6 x_4_7 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2210 (t x_3_10 x_3_5 x_5_10 : ℝ) : ((((x_3_5 ≤ x_3_10) ∧ (x_3_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_5_10)) ≤ ((-1) + t)))) ↔ ((((x_3_5 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_3_5 + ((-1) * x_5_10)) ≤ (-1)) ∧ ((t + x_3_5 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_5_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + ((-1) * x_3_5) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_5_10) ≥ 1)))) := by
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
  have e5 : (x_3_5 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_5_10) ↔ (((1) * x_3_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_10 ≤ x_3_5) ↔ (((1) * x_3_10 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_5_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_5 + ((-1) * x_5_10)) ≤ (-1)) ↔ (((1) * x_3_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_5 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_10 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory2211 (t x_3_4 x_3_5 x_4_5 x_4_6 x_5_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2212 (t x_0_7 x_3_4 x_4_7 x_4_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2213 (t x_0_1 x_1_4 x_1_6 x_2_4 x_3_6 x_4_6 x_4_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2214 (t x_0_9 x_2_6 x_3_7 x_6_7 x_6_9 x_7_9 : ℝ) : (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_9 + ((-1) * x_6_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2215 (t x_0_7 x_2_6 x_3_6 x_3_7 x_6_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_6) + x_3_6) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2216 (t x_5_8 x_6_7 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_8 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2217 (t x_4_7 x_5_6 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2218 (t x_0_4 x_0_7 x_3_6 x_3_7 x_4_5 x_4_6 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2219 (t x_2_4 x_4_10 x_4_8 x_5_8 x_8_10 : ℝ) : (¬ ((t + x_4_8 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_10 + ((-1) * x_8_10)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2221 (t x_3_7 x_3_8 x_6_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2222 (t x_3_7 x_3_9 x_6_7 x_7_8 x_7_9 x_9_10 : ℝ) : (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2223 (t x_3_7 x_3_8 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2224 (t x_0_6 x_0_7 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + x_0_6 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2225 (t x_0_3 x_3_7 x_3_9 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2226 (t x_0_6 x_0_7 x_1_5 x_1_7 x_4_5 x_5_6 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2227 (t x_0_7 x_2_5 x_2_7 x_4_5 x_5_7 x_7_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2228 (t x_1_5 x_3_6 x_4_5 x_4_6 x_5_6 x_6_8 : ℝ) : (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2229 (t x_0_3 x_1_5 x_3_5 x_3_7 x_5_7 : ℝ) : (¬ ((t + ((-1) * x_1_5) + x_3_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2230 (t x_0_3 x_0_5 x_3_4 x_3_5 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2231 (t x_1_5 x_4_5 x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2232 (x_0_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2235 (t x_0_4 x_1_3 x_2_3 x_2_4 x_3_4 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2236 (t x_1_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2237 (t x_0_1 x_0_4 x_1_5 x_2_4 x_4_7 x_4_8 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2238 (t x_0_3 x_1_3 x_1_7 x_3_4 x_3_5 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory2240 (t x_5_8 x_5_9 x_7_8 x_8_9 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2242 (t x_1_3 x_1_5 x_3_4 x_3_5 x_5_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2243 (t x_0_5 x_1_3 x_1_5 x_3_4 x_3_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2244 (t x_0_4 x_2_3 x_2_4 x_3_4 x_3_5 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2245 (t x_4_8 x_5_6 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((t + x_4_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2246 (t x_1_3 x_1_6 x_2_3 x_3_6 x_6_10 : ℝ) : (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2247 (t x_0_1 x_0_4 x_1_5 x_2_4 x_4_7 x_4_8 x_5_6 x_6_8 : ℝ) : (¬ ((t + x_4_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2248 (t x_0_3 x_1_3 x_3_8 x_3_9 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2249 (t x_2_3 x_2_5 x_3_4 x_3_5 x_5_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2250 (t x_0_4 x_1_3 x_2_3 x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2251 (t x_0_4 x_0_6 x_2_4 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2256 (t x_0_9 x_2_5 x_4_7 x_5_7 x_5_9 x_7_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2257 (t x_0_4 x_0_5 x_2_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + x_0_4 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2258 (t x_0_1 x_1_7 x_1_9 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2260 (x_0_3 x_3_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2261 (t x_0_1 x_1_2 x_1_5 x_2_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory2262 (t x_0_9 x_1_7 x_5_7 x_5_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_0_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_7) + x_5_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2263 (t x_0_9 x_2_3 x_3_7 x_3_9 x_5_7 x_7_9 : ℝ) : (¬ ((t + x_3_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_3_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2264 (t x_0_5 x_0_6 x_0_7 x_1_5 x_5_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((t + x_0_5 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2266 (t x_1_5 x_1_7 x_1_8 x_2_5 x_5_8 x_8_10 : ℝ) : (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2267 (t x_2_5 x_3_5 x_3_8 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_5) + x_3_5) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2268 (t x_0_5 x_1_3 x_1_5 x_2_3 x_3_5 x_5_7 : ℝ) : (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2270 (t x_0_2 x_0_3 x_0_5 x_2_3 x_3_4 x_3_7 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_5) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  linarith

theorem theory2271 (t x_1_7 x_1_8 x_4_7 x_5_7 x_7_8 x_8_10 : ℝ) : (¬ ((x_1_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2272 (t x_4_7 x_5_6 x_6_10 x_6_7 x_7_10 : ℝ) : (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((x_6_10 + ((-1) * x_7_10)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2275 (t x_0_6 x_2_5 x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2279 (x_4_8 x_8_10 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_10)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory2281 (t x_0_1 x_1_3 x_1_5 x_3_5 x_3_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_5 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory2283 (t x_0_4 x_1_4 x_2_4 x_2_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2284 (x_0_1 x_0_5 x_0_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_5)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_0_7)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_0_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory2285 (t x_0_2 x_0_5 x_2_3 x_3_4 x_4_7 x_5_7 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_5) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory2290 (t x_0_8 x_3_4 x_4_7 x_4_8 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2291 (t x_0_7 x_1_3 x_1_7 x_2_3 x_3_7 x_7_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory2293 (t x_0_2 x_0_6 x_0_7 x_1_2 x_1_6 x_2_4 x_4_5 x_5_10 x_6_8 x_7_8 x_8_9 x_9_10 : ℝ) : (¬ ((t + x_5_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  linarith

theorem theory2294 (t x_3_4 x_4_5 x_4_8 x_5_10 x_5_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_10)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + x_5_8 + ((-1) * x_5_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

end ElevenTheory
