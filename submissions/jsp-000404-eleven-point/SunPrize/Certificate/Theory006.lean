import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory1490 (x_3_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1491 (x_1_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1492 (t x_0_2 x_0_4 x_2_4 x_2_6 x_4_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1493 (t x_0_4 x_1_7 x_4_7 x_4_9 x_7_9 : ℝ) : (¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1495 (t x_4_10 x_4_7 x_7_10 : ℝ) : ((((x_4_7 ≤ x_4_10) ∧ (x_4_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_4_7 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_4_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_4_7 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_4_7) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((t + x_4_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_4_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_7 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_4_7 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_7 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_7_10) ↔ (((1) * x_4_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_10 ≤ x_4_7) ↔ (((1) * x_4_10 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_7 + ((-1) * x_4_10)) ≥ 0) ↔ (((1) * x_4_10 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_4_7) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_4_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1498 (t x_3_7 x_4_7 x_4_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((t + x_3_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1501 (t x_0_3 x_0_6 x_3_5 x_3_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_6) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1502 (t x_0_4 x_1_3 x_1_4 x_2_3 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1503 (t x_0_4 x_2_3 x_2_4 x_3_4 x_3_7 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1504 (x_2_3 x_3_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1505 (t x_2_4 x_4_5 x_4_6 x_5_6 x_5_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1506 (t x_0_2 x_2_3 x_2_7 x_3_5 x_3_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((t + x_3_5 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1507 (t x_0_1 x_0_2 x_1_2 x_1_5 x_2_3 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1508 (t x_0_2 x_1_3 x_2_3 x_2_7 x_3_4 x_3_7 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1509 (t x_0_2 x_2_5 x_2_7 x_5_6 x_5_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1510 (x_3_4 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1511 (x_0_2 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1512 (t x_0_3 x_0_7 x_1_4 x_1_7 x_3_4 x_3_6 x_7_8 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1513 (t x_1_7 x_3_4 x_4_7 x_4_9 x_7_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1515 (t x_4_5 x_4_6 x_5_6 x_5_7 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1516 (t x_1_5 x_1_6 x_4_5 x_5_6 x_6_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1518 (t x_4_10 x_4_6 x_6_10 : ℝ) : ((((x_4_6 ≤ x_4_10) ∧ (x_4_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_4_6 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_4_6 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((t + x_4_6 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 + ((-1) * x_4_10)) ≥ 0) ↔ (((1) * x_4_10 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_6) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_4_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_6_10) ↔ (((1) * x_4_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_4_10 ≤ x_4_6) ↔ (((1) * x_4_10 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_6 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_4_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_4_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1519 (t x_3_10 x_3_4 x_4_10 : ℝ) : ((((x_3_4 ≤ x_3_10) ∧ (x_3_10 ≤ x_4_10) ∧ ((x_4_10 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_4_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_4_10)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_4_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_4_10) ≥ 1)))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_4_10)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_10 + ((-1) * x_4_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_3_4 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_10 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_4_10) ↔ (((1) * x_3_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_10 ≤ x_3_4) ↔ (((1) * x_3_10 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_10 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_4_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_4 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_4) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_10) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1520 (t x_0_5 x_1_4 x_1_5 x_2_4 x_4_5 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1521 (t x_0_3 x_1_5 x_3_5 x_3_6 x_5_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1523 (t x_4_5 x_5_7 x_5_9 x_7_9 : ℝ) : (¬ ((t + x_5_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory1524 (t x_0_2 x_0_7 x_1_3 x_1_7 x_2_3 x_2_5 x_7_8 : ℝ) : (¬ ((t + x_2_3 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1525 (t x_2_10 x_2_6 x_6_10 : ℝ) : ((((x_2_6 ≤ x_2_10) ∧ (x_2_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_2_6 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_2_6 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((x_2_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_6 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_6) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_6 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_6_10) ↔ (((1) * x_2_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_10 ≤ x_2_6) ↔ (((1) * x_2_10 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_2_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_6 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1526 (t x_3_6 x_3_7 x_5_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1528 (t x_0_7 x_1_5 x_5_7 x_5_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1529 (t x_0_4 x_1_3 x_1_4 x_3_4 x_3_5 x_4_7 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1530 (t x_0_5 x_1_4 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1531 (t x_0_8 x_1_4 x_3_4 x_3_7 x_3_8 x_4_8 x_8_9 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1532 (t x_1_4 x_4_7 x_4_8 x_7_8 x_7_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1533 (t x_0_8 x_6_7 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1534 (t x_0_8 x_1_4 x_2_3 x_3_4 x_3_8 x_4_8 : ℝ) : (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1535 (t x_0_3 x_1_4 x_3_4 x_3_8 x_4_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1536 (t x_0_5 x_5_8 x_5_9 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1537 (t x_0_5 x_1_4 x_2_3 x_3_4 x_3_5 x_4_5 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1539 (t x_0_7 x_1_4 x_3_4 x_3_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1541 (t x_0_2 x_1_4 x_2_4 x_2_5 x_4_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1542 (t x_0_6 x_1_3 x_1_6 x_3_6 x_3_8 x_6_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_6) + x_3_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1543 (t x_0_2 x_0_6 x_2_3 x_3_4 x_4_8 x_5_8 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_5_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory1545 (x_1_3 x_3_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1546 (x_6_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1547 (t x_6_8 x_7_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1548 (t x_3_6 x_3_9 x_5_6 x_6_9 x_9_10 : ℝ) : (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1549 (x_3_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1551 (t x_3_10 x_3_7 x_7_10 : ℝ) : ((((x_3_7 ≤ x_3_10) ∧ (x_3_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_3_7 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_3_7 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_3_7) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((x_3_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_7 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_7) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_7 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_7_10) ↔ (((1) * x_3_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_10 ≤ x_3_7) ↔ (((1) * x_3_10 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_7 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_3_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_7 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1552 (t x_3_6 x_3_7 x_5_6 x_6_7 x_7_10 : ℝ) : (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1553 (t x_7_10 x_7_8 x_8_10 : ℝ) : ((((x_7_8 ≤ x_7_10) ∧ (x_7_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_7_10 + ((-1) * x_7_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_7_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_7_8 + ((-1) * x_7_10)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_7_8 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_7_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_7_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_7_8 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + x_7_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_7_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_7_8 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_7_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_7_8) + x_7_10) ≥ 1) ∧ ((t + ((-1) * x_7_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : ((x_7_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_7_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_7_8 + ((-1) * x_7_10)) ≥ 0) ↔ (((1) * x_7_10 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_7_8) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_7_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_8 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_10 ≤ x_8_10) ↔ (((1) * x_7_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_7_10 ≤ x_7_8) ↔ (((1) * x_7_10 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_10 + ((-1) * x_7_8)) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_8 + ((-1) * x_7_10)) ≤ 0) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_7_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_7_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_7_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_7_8 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_7_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1555 (x_0_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1556 (t x_0_4 x_3_6 x_4_6 x_4_7 x_6_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1557 (t x_0_4 x_1_6 x_4_6 x_4_7 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1558 (x_0_1 x_1_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1559 (t x_0_3 x_1_2 x_1_3 x_2_3 x_2_4 x_3_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1560 (t x_1_7 x_3_7 x_3_9 x_7_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_1_7) + x_3_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1561 (t x_1_2 x_1_6 x_2_4 x_2_6 x_6_8 : ℝ) : (¬ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1562 (t x_0_5 x_4_6 x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1563 (t x_0_6 x_1_4 x_3_4 x_3_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1564 (t x_0_4 x_3_5 x_4_5 x_4_6 x_5_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1565 (t x_0_2 x_1_4 x_2_4 x_2_6 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1566 (t x_1_4 x_2_3 x_3_4 x_3_7 x_4_7 : ℝ) : (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1568 (t x_0_4 x_0_6 x_4_6 x_4_8 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1569 (t x_4_6 x_5_6 x_5_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1570 (t x_0_6 x_1_4 x_4_6 x_4_7 x_6_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1571 (x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1573 (t x_0_6 x_0_7 x_4_6 x_5_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1574 (t x_0_7 x_1_6 x_2_6 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + x_1_6 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1577 (t x_3_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1578 (t x_1_6 x_2_5 x_5_6 x_5_7 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1579 (x_0_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1580 (t x_0_1 x_0_6 x_1_2 x_1_5 x_1_6 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_1_2) + x_1_5) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1581 (t x_0_6 x_1_6 x_3_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1583 (t x_0_4 x_0_6 x_1_3 x_1_6 x_3_4 x_3_5 x_6_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1584 (t x_0_4 x_0_6 x_1_3 x_1_6 x_2_3 x_3_4 x_6_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1587 (t x_0_6 x_4_5 x_4_6 x_5_6 x_5_8 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_8) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1589 (t x_1_5 x_1_6 x_4_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1590 (x_0_1 x_1_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1591 (t x_0_1 x_1_6 x_1_7 x_4_6 x_6_7 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1592 (x_1_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1593 (t x_0_1 x_0_4 x_1_2 x_1_4 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1594 (t x_1_5 x_4_6 x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1596 (t x_1_5 x_4_6 x_5_6 x_5_7 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1597 (x_4_6 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1598 (t x_0_3 x_3_6 x_3_8 x_4_6 x_6_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1599 (t x_0_6 x_5_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1601 (t x_0_6 x_3_5 x_3_6 x_5_6 x_5_7 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_7) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1603 (x_0_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1604 (t x_0_2 x_0_3 x_0_4 x_2_4 x_3_5 x_4_7 x_4_9 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_9) + x_8_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory1605 (t x_0_1 x_1_4 x_1_7 x_3_4 x_4_7 : ℝ) : (¬ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1606 (t x_0_1 x_0_4 x_1_2 x_1_3 x_1_4 x_4_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1607 (t x_5_10 x_5_8 x_8_10 : ℝ) : ((((x_5_8 ≤ x_5_10) ∧ (x_5_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_5_8 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_5_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_5_8 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_5_8 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_5_8) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : (x_5_8 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_10 ≤ x_8_10) ↔ (((1) * x_5_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_8_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_5_10 ≤ x_5_8) ↔ (((1) * x_5_10 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_10 + ((-1) * x_5_8)) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_10 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_8_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_8 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 + ((-1) * x_5_10)) ≤ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_5_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_5_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_5_8 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_5_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_8 + ((-1) * x_5_10)) ≥ 0) ↔ (((1) * x_5_10 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_5_8) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_5_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1608 (t x_6_10 x_6_8 x_8_10 : ℝ) : ((((x_6_8 ≤ x_6_10) ∧ (x_6_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_6_8 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_6_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_6_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_6_8 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + x_6_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_6_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_6_8 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_6_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_6_8) + x_6_10) ≥ 1) ∧ ((t + ((-1) * x_6_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : ((x_6_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_6_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_8 + ((-1) * x_6_10)) ≥ 0) ↔ (((1) * x_6_10 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_6_8) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_6_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_8 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_8_10) ↔ (((1) * x_6_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_10 ≤ x_6_8) ↔ (((1) * x_6_10 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_10 + ((-1) * x_6_8)) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_8 + ((-1) * x_6_10)) ≤ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_6_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_6_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_6_8 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_6_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1609 (t x_0_2 x_0_3 x_2_4 x_3_5 x_4_7 x_5_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory1610 (x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1611 (t x_0_1 x_0_2 x_1_2 x_1_5 x_2_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1612 (t x_1_2 x_1_4 x_2_4 x_2_5 x_4_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1613 (t x_0_1 x_1_2 x_1_4 x_2_4 x_2_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1614 (t x_1_2 x_1_7 x_2_3 x_2_7 x_7_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_7) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1615 (x_1_4 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1616 (t x_2_7 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1618 (t x_0_5 x_0_6 x_3_4 x_3_6 x_4_5 x_4_7 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1619 (t x_0_2 x_0_3 x_1_2 x_1_3 x_2_7 x_2_9 x_3_5 x_5_8 x_7_9 x_8_9 x_9_10 : ℝ) : (¬ ((x_2_7 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  linarith

theorem theory1620 (t x_0_3 x_0_4 x_2_7 x_3_5 x_4_7 x_5_8 x_7_9 x_8_10 x_9_10 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_4) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory1621 (x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1622 (t x_0_10 x_0_8 x_8_10 : ℝ) : ((((x_0_8 ≤ x_0_10) ∧ (x_0_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_0_8)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_8) ∧ ((x_0_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_0_8 + ((-1) * x_0_10)) ≤ 0) ∧ ((x_0_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_0_8 + ((-1) * x_0_10)) ≥ 1) ∧ ((t + x_0_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_0_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_0_8 + ((-1) * x_0_10)) ≥ 0) ∧ ((x_0_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_0_10) ≥ 1) ∧ ((t + ((-1) * x_0_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : ((x_0_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_8) + x_0_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_8 + ((-1) * x_0_10)) ≥ 0) ↔ (((1) * x_0_10 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_8 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_10 ≤ x_8_10) ↔ (((1) * x_0_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_10 ≤ x_0_8) ↔ (((1) * x_0_10 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_10 + ((-1) * x_0_8)) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_10 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_8 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_0_10)) ≤ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_0_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_0_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_8 + ((-1) * x_0_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1623 (x_5_6 x_6_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1624 (t x_5_6 x_5_9 x_6_7 x_6_9 x_9_10 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_9)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1625 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_7 x_3_5 x_5_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_7_9) + x_8_9) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  linarith

theorem theory1626 (t x_0_1 x_0_2 x_1_2 x_1_3 x_2_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1627 (t x_0_1 x_1_2 x_1_7 x_2_3 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_7) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1628 (t x_0_1 x_1_2 x_1_6 x_2_3 x_2_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_6) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1629 (t x_0_2 x_0_3 x_2_7 x_3_5 x_5_8 x_7_9 x_8_10 x_9_10 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_3)) ≥ 1)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory1630 (x_5_6 x_6_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1631 (x_4_9 x_9_10 : ℝ) : (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1632 (t x_3_10 x_3_8 x_8_10 : ℝ) : ((((x_3_8 ≤ x_3_10) ∧ (x_3_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_3_8 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_3_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_3_8 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_3_8 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_3_8) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : ((x_3_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_8 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_8) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_8 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_8_10) ↔ (((1) * x_3_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_10 ≤ x_3_8) ↔ (((1) * x_3_10 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_10 + ((-1) * x_3_8)) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_8 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_3_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_8 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1633 (t x_2_10 x_2_8 x_8_10 : ℝ) : ((((x_2_8 ≤ x_2_10) ∧ (x_2_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_8_10)) ≤ ((-1) + t)))) ↔ ((((x_2_8 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_8_10)) ≤ (-1)) ∧ ((t + x_2_8 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_8_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_8_10) ≥ 1)))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_10 + ((-1) * x_8_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_8 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_8) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_10) + x_8_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_8 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_8_10) ↔ (((1) * x_2_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_10 ≤ x_2_8) ↔ (((1) * x_2_10 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_10 + ((-1) * x_2_8)) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_8 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_8 + ((-1) * x_8_10)) ≤ (-1)) ↔ (((1) * x_2_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_8 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_10 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1634 (x_3_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1635 (t x_0_2 x_0_4 x_0_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1636 (t x_0_7 x_4_8 x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_4_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1637 (x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1638 (t x_0_6 x_3_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((t + x_3_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1640 (x_0_1 x_0_2 x_0_4 : ℝ) : ((x_0_2 + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1642 (t x_0_4 x_0_6 x_1_3 x_3_6 x_3_7 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1643 (t x_0_4 x_1_2 x_2_4 x_2_7 x_4_5 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1644 (x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1645 (t x_2_8 x_2_9 x_5_8 x_8_9 x_9_10 : ℝ) : (¬ ((t + ((-1) * x_2_8) + x_5_8) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_2_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1646 (t x_4_5 x_5_8 x_5_9 x_6_8 x_8_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_5_8 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1647 (t x_1_2 x_2_8 x_2_9 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_8) + x_5_8) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1648 (t x_0_1 x_0_2 x_1_2 x_1_7 x_2_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1649 (t x_0_8 x_1_2 x_2_8 x_2_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_8) + x_2_8) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_2_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1651 (t x_0_6 x_4_7 x_6_7 x_6_9 x_7_9 : ℝ) : (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1652 (x_0_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1653 (t x_1_5 x_4_6 x_5_6 x_5_9 x_6_9 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1654 (t x_0_1 x_0_4 x_0_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1655 (t x_0_5 x_0_6 x_4_6 x_5_6 x_5_9 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1656 (x_0_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1657 (t x_0_7 x_1_6 x_1_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1658 (t x_0_5 x_2_3 x_2_5 x_3_4 x_3_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_5) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1659 (x_0_5 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1660 (x_1_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1663 (t x_1_5 x_3_6 x_4_5 x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1667 (t x_1_2 x_1_9 x_2_3 x_2_9 x_9_10 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_9) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1668 (t x_1_3 x_3_5 x_3_6 x_4_6 x_5_6 x_5_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1669 (t x_1_4 x_1_5 x_4_5 x_4_7 x_5_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1670 (t x_0_8 x_1_6 x_2_6 x_2_8 x_6_8 x_8_9 : ℝ) : (¬ ((t + x_1_6 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1671 (x_2_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1672 (t x_0_5 x_1_3 x_1_5 x_2_3 x_3_5 x_5_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1673 (x_1_5 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1674 (x_4_6 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1675 (x_0_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1677 (x_1_6 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1678 (t x_1_6 x_5_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1683 (t x_0_1 x_0_3 x_1_3 x_3_7 x_3_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1684 (t x_0_4 x_1_3 x_1_4 x_3_4 x_3_7 x_4_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1685 (t x_0_2 x_0_3 x_2_3 x_2_5 x_3_6 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1686 (t x_0_2 x_2_3 x_2_4 x_3_4 x_3_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_6) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1687 (t x_0_1 x_0_3 x_1_7 x_3_5 x_5_6 x_6_9 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_8_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory1688 (t x_0_4 x_1_8 x_4_7 x_4_8 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_4_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1689 (t x_0_7 x_3_6 x_3_7 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_3_6 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1690 (t x_0_6 x_0_7 x_1_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1691 (t x_2_5 x_5_7 x_5_8 x_7_8 x_7_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1692 (x_0_4 x_2_4 x_3_4 : ℝ) : (¬ ((x_2_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1693 (t x_1_10 x_1_6 x_6_10 : ℝ) : ((((x_1_6 ≤ x_1_10) ∧ (x_1_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_1_6 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_6 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_6) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_6 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_10 ≤ x_6_10) ↔ (((1) * x_1_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_10 ≤ x_1_6) ↔ (((1) * x_1_10 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_6 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1694 (t x_0_10 x_0_7 x_7_10 : ℝ) : ((((x_0_7 ≤ x_0_10) ∧ (x_0_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_0_7 + ((-1) * x_0_10)) ≤ 0) ∧ ((x_0_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_0_7 + ((-1) * x_0_10)) ≥ 1) ∧ ((t + x_0_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_0_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_0_10)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_0_10) ≥ 1) ∧ ((t + ((-1) * x_0_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_0_10)) ≤ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_0_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_7 + ((-1) * x_0_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_0_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_7 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_10 ≤ x_7_10) ↔ (((1) * x_0_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_10 ≤ x_0_7) ↔ (((1) * x_0_10 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_10 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_7 + ((-1) * x_0_10)) ≥ 0) ↔ (((1) * x_0_10 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_7) + x_0_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1695 (x_0_6 x_1_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1696 (t x_1_7 x_3_6 x_3_7 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1697 (t x_0_6 x_1_4 x_2_3 x_3_4 x_3_6 x_4_6 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1698 (x_0_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1699 (t x_0_3 x_3_6 x_3_7 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_3_6) + x_5_6) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1700 (t x_0_1 x_0_3 x_1_8 x_3_5 x_5_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory1701 (t x_1_2 x_1_8 x_2_4 x_2_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1702 (t x_3_7 x_6_7 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1705 (t x_1_10 x_1_7 x_7_10 : ℝ) : ((((x_1_7 ≤ x_1_10) ∧ (x_1_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_1_7 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_1_7 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((x_1_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_7) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_7 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_10 ≤ x_7_10) ↔ (((1) * x_1_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_10 ≤ x_1_7) ↔ (((1) * x_1_10 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_7 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_1_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_7 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1706 (t x_1_6 x_1_7 x_6_7 x_6_8 x_7_10 : ℝ) : (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1708 (t x_1_7 x_2_5 x_2_7 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_7)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1709 (t x_0_5 x_5_7 x_5_9 x_7_8 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_7_8 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1710 (t x_1_6 x_4_5 x_4_6 x_5_6 x_5_7 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1713 (t x_0_6 x_1_4 x_2_4 x_2_6 x_4_6 x_6_7 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1714 (t x_3_5 x_3_7 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_7)) ≤ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1715 (t x_1_3 x_2_4 x_3_4 x_3_7 x_4_7 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1716 (t x_2_3 x_3_6 x_3_8 x_6_7 x_6_8 : ℝ) : (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1719 (t x_0_3 x_0_6 x_2_3 x_3_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + x_0_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1720 (x_0_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1721 (x_1_2 x_2_3 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1722 (t x_0_7 x_1_4 x_3_6 x_4_6 x_4_7 x_6_7 : ℝ) : (¬ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1723 (t x_0_6 x_1_3 x_2_3 x_2_6 x_3_6 x_6_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1724 (t x_0_10 x_0_6 x_6_10 : ℝ) : ((((x_0_6 ≤ x_0_10) ∧ (x_0_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_0_6 + ((-1) * x_0_10)) ≤ 0) ∧ ((x_0_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_10)) ≥ 1) ∧ ((t + x_0_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_0_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_10)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_10) ≥ 1) ∧ ((t + ((-1) * x_0_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_0_10)) ≥ 0) ↔ (((1) * x_0_10 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_6) + x_0_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_6 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_10 ≤ x_6_10) ↔ (((1) * x_0_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_10 ≤ x_0_6) ↔ (((1) * x_0_10 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_10 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_10)) ≤ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_0_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_6 + ((-1) * x_0_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1727 (t x_3_4 x_3_8 x_4_6 x_4_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_4_6) + x_4_8) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1729 (t x_2_6 x_2_7 x_6_7 x_6_8 x_7_9 : ℝ) : (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1731 (t x_1_3 x_3_4 x_3_5 x_4_5 x_4_6 : ℝ) : (¬ ((t + x_4_5 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1732 (t x_0_2 x_2_7 x_2_8 x_5_7 x_7_8 : ℝ) : (¬ ((x_2_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1735 (t x_0_3 x_3_7 x_3_8 x_6_7 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_3_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1736 (t x_0_2 x_0_3 x_2_3 x_2_4 x_3_5 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1737 (t x_0_3 x_3_7 x_3_8 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1738 (t x_0_2 x_1_3 x_2_3 x_2_6 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1739 (t x_0_2 x_1_3 x_2_3 x_2_5 x_3_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1740 (x_0_3 x_1_3 x_2_3 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_2_3)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1741 (x_0_1 x_1_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

end ElevenTheory
