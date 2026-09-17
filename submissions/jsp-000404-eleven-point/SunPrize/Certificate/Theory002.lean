import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory420 (x_0_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory421 (x_0_6 x_1_6 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory422 (x_3_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory423 (x_0_1 x_0_5 x_1_4 x_1_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory424 (t x_5_9 x_7_9 x_8_9 : ℝ) : (¬ ((x_5_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_5_9) + x_7_9) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory425 (x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory426 (x_0_1 x_1_2 x_1_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory427 (x_0_3 x_3_4 x_3_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory428 (x_0_2 x_0_4 x_2_4 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory429 (x_0_2 x_1_2 x_2_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory430 (x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory431 (t x_1_6 x_4_6 x_5_6 : ℝ) : (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((t + x_4_6 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory432 (x_0_7 x_0_8 x_2_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory433 (t x_5_10 x_5_8 x_8_10 : ℝ) : ((((x_5_8 ≤ x_5_10) ∧ (x_5_10 ≤ x_8_10) ∧ ((x_8_10 - x_5_8) ≥ 1) ∧ ((x_5_10 - x_5_8) ≤ (t - 1)) ∧ ((x_8_10 - x_5_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_8) ∧ ((x_5_8 - x_8_10) ≥ 1) ∧ ((x_5_8 - x_5_10) ≤ (t - 1)) ∧ ((x_5_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_5_8 ≤ x_5_10) ∧ (x_5_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_5_8 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_10 ≤ x_8_10) ↔ (((1) * x_5_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_8_10 - x_5_8) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_10 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_8_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_5_8) ↔ (((1) * x_5_10 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_8 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_10 + ((-1) * x_5_8)) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_8 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory434 (t x_6_10 x_6_8 x_8_10 : ℝ) : ((((x_6_8 ≤ x_6_10) ∧ (x_6_10 ≤ x_8_10) ∧ ((x_8_10 - x_6_8) ≥ 1) ∧ ((x_6_10 - x_6_8) ≤ (t - 1)) ∧ ((x_8_10 - x_6_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_8) ∧ ((x_6_8 - x_8_10) ≥ 1) ∧ ((x_6_8 - x_6_10) ≤ (t - 1)) ∧ ((x_6_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_6_8 ≤ x_6_10) ∧ (x_6_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_6_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_8 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_6_10 ≤ x_8_10) ↔ (((1) * x_6_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_6_8) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_10 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_10 ≤ x_6_8) ↔ (((1) * x_6_10 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_6_8)) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_10 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_8 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory435 (t x_8_10 : ℝ) : ((¬ (t ≤ x_8_10)) ↔ (¬ ((t + ((-1) * x_8_10)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_8_10) ↔ (((1) * t + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_8_10)) ≤ 0) ↔ (((1) * t + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory436 (x_0_3 x_0_6 x_3_6 x_4_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory437 (x_0_2 x_1_2 x_2_5 x_2_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory438 (x_0_3 x_1_3 x_2_3 : ℝ) : (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ ((x_0_3 + ((-1) * x_2_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory441 (x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory446 (t x_0_10 x_0_8 x_8_10 : ℝ) : ((((x_0_8 ≤ x_0_10) ∧ (x_0_10 ≤ x_8_10) ∧ ((x_8_10 - x_0_8) ≥ 1) ∧ ((x_0_10 - x_0_8) ≤ (t - 1)) ∧ ((x_8_10 - x_0_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_8) ∧ ((x_0_8 - x_8_10) ≥ 1) ∧ ((x_0_8 - x_0_10) ≤ (t - 1)) ∧ ((x_0_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_0_8 ≤ x_0_10) ∧ (x_0_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_0_8)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_8) ∧ ((x_0_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_8 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_10 ≤ x_8_10) ↔ (((1) * x_0_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_0_8) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_10 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_10 ≤ x_0_8) ↔ (((1) * x_0_10 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_8 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_0_8)) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_10 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory448 (x_1_4 x_1_6 x_4_5 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory449 (x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory450 (t x_3_10 x_3_8 x_8_10 : ℝ) : ((((x_3_8 ≤ x_3_10) ∧ (x_3_10 ≤ x_8_10) ∧ ((x_8_10 - x_3_8) ≥ 1) ∧ ((x_3_10 - x_3_8) ≤ (t - 1)) ∧ ((x_8_10 - x_3_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_8) ∧ ((x_3_8 - x_8_10) ≥ 1) ∧ ((x_3_8 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_3_8 ≤ x_3_10) ∧ (x_3_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_10 ≤ x_8_10) ↔ (((1) * x_3_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_3_8) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_10 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_3_8) ↔ (((1) * x_3_10 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_3_8)) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_10 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_8 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory451 (t x_2_10 x_2_8 x_8_10 : ℝ) : ((((x_2_8 ≤ x_2_10) ∧ (x_2_10 ≤ x_8_10) ∧ ((x_8_10 - x_2_8) ≥ 1) ∧ ((x_2_10 - x_2_8) ≤ (t - 1)) ∧ ((x_8_10 - x_2_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_8) ∧ ((x_2_8 - x_8_10) ≥ 1) ∧ ((x_2_8 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_2_8 ≤ x_2_10) ∧ (x_2_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_8 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_10 ≤ x_8_10) ↔ (((1) * x_2_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_2_8) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_10 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_10 ≤ x_2_8) ↔ (((1) * x_2_10 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_2_8)) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_10 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory454 (x_4_6 x_4_9 x_6_8 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory455 (t x_1_9 : ℝ) : ((¬ (t ≤ x_1_9)) ↔ (¬ ((t + ((-1) * x_1_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_9) ↔ (((1) * t + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * t + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory456 (x_1_6 x_2_6 x_6_7 : ℝ) : (¬ ((x_1_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory458 (x_1_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≤ 0)) ∨ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory459 (x_1_9 x_2_10 x_2_9 x_9_10 : ℝ) : (¬ ((x_2_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_2_10)) ≤ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_2_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory461 (x_0_5 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory465 (x_1_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory466 (x_0_3 x_2_3 x_3_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory467 (x_3_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory468 (x_0_6 x_0_9 x_3_6 x_6_9 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_6_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory469 (x_0_5 x_3_5 : ℝ) : ((x_0_5 + ((-1) * x_3_5)) ≤ 0) ∨ ((x_0_5 + ((-1) * x_3_5)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory471 (t x_3_8 x_5_8 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_3_8) + x_7_8) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ ((t + ((-1) * x_3_8) + x_5_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory472 (x_0_3 x_2_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory473 (x_1_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory474 (t x_1_10 x_1_6 x_6_10 : ℝ) : ((((x_1_6 ≤ x_1_10) ∧ (x_1_10 ≤ x_6_10) ∧ ((x_6_10 - x_1_6) ≥ 1) ∧ ((x_1_10 - x_1_6) ≤ (t - 1)) ∧ ((x_6_10 - x_1_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_6) ∧ ((x_1_6 - x_6_10) ≥ 1) ∧ ((x_1_6 - x_1_10) ≤ (t - 1)) ∧ ((x_1_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_1_6 ≤ x_1_10) ∧ (x_1_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_6 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_10 ≤ x_6_10) ↔ (((1) * x_1_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_1_6) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_10 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_10 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_10 ≤ x_1_6) ↔ (((1) * x_1_10 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_6 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_10 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory475 (t x_0_10 x_0_7 x_7_10 : ℝ) : ((((x_0_7 ≤ x_0_10) ∧ (x_0_10 ≤ x_7_10) ∧ ((x_7_10 - x_0_7) ≥ 1) ∧ ((x_0_10 - x_0_7) ≤ (t - 1)) ∧ ((x_7_10 - x_0_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_7) ∧ ((x_0_7 - x_7_10) ≥ 1) ∧ ((x_0_7 - x_0_10) ≤ (t - 1)) ∧ ((x_0_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_0_7 ≤ x_0_10) ∧ (x_0_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_7 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_10 ≤ x_7_10) ↔ (((1) * x_0_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_10 - x_0_7) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_10 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_10 ≤ x_0_7) ↔ (((1) * x_0_10 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_7 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_10 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory476 (x_0_7 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory477 (x_0_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory478 (t x_1_10 x_1_7 x_7_10 : ℝ) : ((((x_1_7 ≤ x_1_10) ∧ (x_1_10 ≤ x_7_10) ∧ ((x_7_10 - x_1_7) ≥ 1) ∧ ((x_1_10 - x_1_7) ≤ (t - 1)) ∧ ((x_7_10 - x_1_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_7) ∧ ((x_1_7 - x_7_10) ≥ 1) ∧ ((x_1_7 - x_1_10) ≤ (t - 1)) ∧ ((x_1_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_1_7 ≤ x_1_10) ∧ (x_1_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_10 ≤ x_7_10) ↔ (((1) * x_1_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_10 - x_1_7) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_10 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_10 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_10 ≤ x_1_7) ↔ (((1) * x_1_10 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_10 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory479 (x_0_2 x_2_6 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_8)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory480 (x_0_1 x_0_4 x_1_5 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory481 (x_0_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory482 (t x_0_8 : ℝ) : ((¬ (t ≤ x_0_8)) ↔ (¬ ((t + ((-1) * x_0_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_8) ↔ (((1) * t + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * t + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory483 (t x_0_10 x_0_6 x_6_10 : ℝ) : ((((x_0_6 ≤ x_0_10) ∧ (x_0_10 ≤ x_6_10) ∧ ((x_6_10 - x_0_6) ≥ 1) ∧ ((x_0_10 - x_0_6) ≤ (t - 1)) ∧ ((x_6_10 - x_0_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_6) ∧ ((x_0_6 - x_6_10) ≥ 1) ∧ ((x_0_6 - x_0_10) ≤ (t - 1)) ∧ ((x_0_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_0_6 ≤ x_0_10) ∧ (x_0_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_6 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_10 ≤ x_6_10) ↔ (((1) * x_0_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_0_6) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_10 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_10 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_10 ≤ x_0_6) ↔ (((1) * x_0_10 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_6 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_10 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory487 (x_0_2 x_0_4 x_2_7 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory488 (x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory489 (x_0_2 x_1_2 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory490 (x_1_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_1_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory491 (x_1_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory492 (x_0_1 x_1_4 x_1_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory493 (x_1_3 x_2_3 : ℝ) : ((x_1_3 + ((-1) * x_2_3)) ≤ 0) ∨ ((x_1_3 + ((-1) * x_2_3)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory494 (x_0_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory495 (x_6_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory496 (x_0_1 x_0_4 x_0_5 x_1_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory497 (x_0_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory498 (x_0_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory499 (x_1_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory501 (x_0_6 x_0_8 x_6_7 x_6_8 : ℝ) : (¬ ((x_0_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory502 (x_0_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory503 (x_0_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≥ 0)) ∨ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory504 (x_0_1 x_0_3 x_1_4 x_3_4 : ℝ) : (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory506 (x_0_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory507 (x_0_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory508 (x_0_8 x_3_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory509 (x_0_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory510 (x_0_3 x_3_4 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory511 (x_1_4 x_3_4 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory512 (t x_5_10 x_5_7 x_7_10 : ℝ) : ((((x_5_7 ≤ x_5_10) ∧ (x_5_10 ≤ x_7_10) ∧ ((x_7_10 - x_5_7) ≥ 1) ∧ ((x_5_10 - x_5_7) ≤ (t - 1)) ∧ ((x_7_10 - x_5_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_7) ∧ ((x_5_7 - x_7_10) ≥ 1) ∧ ((x_5_7 - x_5_10) ≤ (t - 1)) ∧ ((x_5_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_5_7 ≤ x_5_10) ∧ (x_5_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_7 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_10 ≤ x_7_10) ↔ (((1) * x_5_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_10 - x_5_7) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_10 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_10 ≤ x_5_7) ↔ (((1) * x_5_10 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_5_7)) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_10 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_7 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory516 (x_4_6 x_4_7 x_6_8 x_6_9 x_7_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory519 (x_5_10 x_5_7 x_6_7 x_7_10 : ℝ) : (¬ ((x_5_10 + ((-1) * x_7_10)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory520 (t x_4_10 x_4_8 x_8_10 : ℝ) : ((((x_4_8 ≤ x_4_10) ∧ (x_4_10 ≤ x_8_10) ∧ ((x_8_10 - x_4_8) ≥ 1) ∧ ((x_4_10 - x_4_8) ≤ (t - 1)) ∧ ((x_8_10 - x_4_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_8) ∧ ((x_4_8 - x_8_10) ≥ 1) ∧ ((x_4_8 - x_4_10) ≤ (t - 1)) ∧ ((x_4_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_4_8 ≤ x_4_10) ∧ (x_4_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_4_8 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_10 ≤ x_8_10) ↔ (((1) * x_4_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_8_10 - x_4_8) ≥ 1) ↔ (((1) * x_4_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_10 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_8_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_4_8) ↔ (((1) * x_4_10 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_8 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_10 + ((-1) * x_4_8)) ≥ 1) ↔ (((1) * x_4_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_8 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory522 (x_1_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory523 (x_0_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory525 (x_0_3 x_3_6 x_3_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_0_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory528 (t x_4_8 x_5_8 x_6_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_5_8) + x_6_8) ≥ 1)) ∨ ((t + x_4_8 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory529 (x_0_3 x_3_4 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_8)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory530 (t x_2_10 x_2_4 x_4_10 : ℝ) : ((((x_2_4 ≤ x_2_10) ∧ (x_2_10 ≤ x_4_10) ∧ ((x_4_10 - x_2_4) ≥ 1) ∧ ((x_2_10 - x_2_4) ≤ (t - 1)) ∧ ((x_4_10 - x_2_10) ≤ (t - 1))) ∨ ((x_4_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_4) ∧ ((x_2_4 - x_4_10) ≥ 1) ∧ ((x_2_4 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_4_10) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_10) ∧ (x_2_10 ≤ x_4_10) ∧ ((x_4_10 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_4_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_4_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_4 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_10 ≤ x_4_10) ↔ (((1) * x_2_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_10 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_10 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_2_4) ↔ (((1) * x_2_10 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 - x_4_10) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_10 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory531 (x_1_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory533 (x_0_1 x_0_3 x_1_4 x_3_4 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≤ 0)) ∨ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory536 (x_2_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory537 (x_0_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory538 (x_0_1 x_0_5 x_1_6 x_5_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory539 (x_1_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory540 (t x_1_10 x_1_8 x_8_10 : ℝ) : ((((x_1_8 ≤ x_1_10) ∧ (x_1_10 ≤ x_8_10) ∧ ((x_8_10 - x_1_8) ≥ 1) ∧ ((x_1_10 - x_1_8) ≤ (t - 1)) ∧ ((x_8_10 - x_1_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_8) ∧ ((x_1_8 - x_8_10) ≥ 1) ∧ ((x_1_8 - x_1_10) ≤ (t - 1)) ∧ ((x_1_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_1_8 ≤ x_1_10) ∧ (x_1_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_1_8)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_8) ∧ ((x_1_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_10 ≤ x_8_10) ↔ (((1) * x_1_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_1_8) ≥ 1) ↔ (((1) * x_1_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_10 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_10 ≤ x_1_8) ↔ (((1) * x_1_10 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_1_8)) ≥ 1) ↔ (((1) * x_1_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_10 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_8 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory542 (x_1_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ ((x_1_3 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory544 (x_2_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory545 (x_3_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory547 (x_2_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory548 (x_2_3 x_3_4 x_3_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory549 (x_0_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory550 (x_0_1 x_1_2 x_1_3 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory551 (x_0_6 x_2_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory552 (x_4_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory553 (x_0_2 x_0_5 x_2_8 x_5_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_2_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory554 (x_0_1 x_1_7 x_1_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory555 (x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory556 (x_0_6 x_2_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory557 (x_4_6 x_5_6 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) ∨ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory558 (x_3_9 x_6_9 x_9_10 : ℝ) : (¬ ((x_3_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory559 (x_0_3 x_2_3 x_3_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory560 (x_4_6 x_4_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory561 (x_4_5 x_5_7 x_5_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_4_5 + ((-1) * x_5_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory562 (x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory564 (x_1_2 x_2_5 x_2_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_6)) ≤ 0)) ∨ ((x_1_2 + ((-1) * x_2_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory565 (x_1_5 x_4_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory567 (x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_4_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory568 (x_0_7 x_3_7 x_5_7 : ℝ) : (¬ ((x_0_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ ((x_3_7 + ((-1) * x_5_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory569 (x_2_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory570 (x_0_7 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory571 (x_0_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory572 (x_0_3 x_0_6 x_3_5 x_3_6 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory573 (x_3_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory574 (x_3_5 x_3_6 x_3_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_3_8)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_3_8)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory577 (x_1_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory578 (x_0_1 x_1_4 x_1_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory579 (x_4_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory581 (x_3_6 x_6_7 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≤ 0)) ∨ ((x_3_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory582 (x_4_5 x_5_8 x_5_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_5_9)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_5_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory585 (t x_6_10 : ℝ) : ((¬ (t ≤ x_6_10)) ↔ (¬ ((t + ((-1) * x_6_10)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_6_10) ↔ (((1) * t + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * t + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory586 (x_0_5 x_0_9 x_3_5 x_5_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_5_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory587 (x_1_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory588 (x_0_1 x_0_4 x_1_5 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)) ∨ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory590 (x_0_6 x_1_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory592 (x_0_6 x_1_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory594 (t x_3_10 x_3_6 x_6_10 : ℝ) : ((((x_3_6 ≤ x_3_10) ∧ (x_3_10 ≤ x_6_10) ∧ ((x_6_10 - x_3_6) ≥ 1) ∧ ((x_3_10 - x_3_6) ≤ (t - 1)) ∧ ((x_6_10 - x_3_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_6) ∧ ((x_3_6 - x_6_10) ≥ 1) ∧ ((x_3_6 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_3_6 ≤ x_3_10) ∧ (x_3_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_10 ≤ x_6_10) ↔ (((1) * x_3_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_3_6) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_10 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_3_6) ↔ (((1) * x_3_10 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_10 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory595 (x_0_5 x_1_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory597 (x_0_1 x_0_2 : ℝ) : ((x_0_1 + ((-1) * x_0_2)) ≥ 0) ∨ ((x_0_1 + ((-1) * x_0_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory600 (x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory603 (x_0_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory608 (x_1_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory611 (x_0_5 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory612 (x_1_4 x_2_4 x_4_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory613 (x_0_2 x_1_2 x_2_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory614 (x_1_5 x_2_5 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory615 (x_0_4 x_3_4 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory617 (x_1_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory618 (x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ ((x_4_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory620 (x_0_1 x_1_3 x_1_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory622 (x_0_1 x_1_4 x_1_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory623 (x_0_7 x_2_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory624 (t x_2_10 x_2_7 x_7_10 : ℝ) : ((((x_2_7 ≤ x_2_10) ∧ (x_2_10 ≤ x_7_10) ∧ ((x_7_10 - x_2_7) ≥ 1) ∧ ((x_2_10 - x_2_7) ≤ (t - 1)) ∧ ((x_7_10 - x_2_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_7) ∧ ((x_2_7 - x_7_10) ≥ 1) ∧ ((x_2_7 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_2_7 ≤ x_2_10) ∧ (x_2_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_7 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_10 ≤ x_7_10) ↔ (((1) * x_2_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_10 - x_2_7) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_10 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_2_7) ↔ (((1) * x_2_10 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_7 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_10 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_7 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory627 (x_3_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory628 (x_0_6 x_4_6 x_6_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory629 (x_0_5 x_1_5 : ℝ) : ((x_0_5 + ((-1) * x_1_5)) ≤ 0) ∨ ((x_0_5 + ((-1) * x_1_5)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory630 (x_0_1 x_0_2 x_0_5 x_1_5 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory631 (x_0_3 x_1_3 x_3_4 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory632 (x_2_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_2_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory633 (x_0_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory637 (x_1_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory638 (x_3_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory645 (x_1_7 x_2_7 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory649 (x_0_1 x_0_5 x_1_7 x_5_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory650 (x_6_7 x_6_8 : ℝ) : ((x_6_7 + ((-1) * x_6_8)) ≤ 0) ∨ ((x_6_7 + ((-1) * x_6_8)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory653 (x_0_4 x_2_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory654 (x_0_4 x_4_6 x_4_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory655 (x_0_2 x_0_5 x_0_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ ((x_0_2 + ((-1) * x_0_8)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory657 (x_0_1 x_1_3 x_1_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory658 (x_0_4 x_0_9 x_3_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_9 + ((-1) * x_4_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory662 (t x_3_10 x_3_5 x_5_10 : ℝ) : ((((x_3_5 ≤ x_3_10) ∧ (x_3_10 ≤ x_5_10) ∧ ((x_5_10 - x_3_5) ≥ 1) ∧ ((x_3_10 - x_3_5) ≤ (t - 1)) ∧ ((x_5_10 - x_3_10) ≤ (t - 1))) ∨ ((x_5_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_5) ∧ ((x_3_5 - x_5_10) ≥ 1) ∧ ((x_3_5 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_5_10) ≤ (t - 1)))) ↔ (((x_3_5 ≤ x_3_10) ∧ (x_3_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_5_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_5 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_10 ≤ x_5_10) ↔ (((1) * x_3_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_10 - x_3_5) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_10 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_3_5) ↔ (((1) * x_3_10 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_5 - x_5_10) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_5 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_10 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory663 (x_1_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory664 (t x_4_7 x_5_7 x_6_7 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory667 (x_0_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory668 (x_0_3 x_3_5 x_3_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory670 (x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory671 (x_0_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory672 (t x_3_7 x_4_7 x_5_7 : ℝ) : (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + x_3_7 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory674 (x_0_7 x_3_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory675 (x_0_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory676 (x_1_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ ((x_2_3 + ((-1) * x_3_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory678 (x_0_1 x_1_3 x_1_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_4)) ≥ 0)) ∨ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory679 (x_3_5 x_5_7 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory680 (x_1_5 x_3_5 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory682 (x_0_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory683 (x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory686 (x_4_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_4_7 + ((-1) * x_7_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory687 (x_0_1 x_1_3 x_1_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory688 (x_1_8 x_3_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((x_1_8 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory691 (x_0_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory692 (x_0_10 x_0_8 x_3_8 x_8_10 : ℝ) : (¬ ((x_0_8 + ((-1) * x_0_10)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0)) ∨ (¬ ((x_0_10 + ((-1) * x_8_10)) ≤ 0)) ∨ (¬ ((x_3_8 + ((-1) * x_8_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory695 (x_0_2 x_2_3 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory696 (x_1_3 x_2_3 x_3_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory697 (x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory700 (x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory701 (x_1_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory702 (x_4_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory703 (x_2_3 x_3_5 x_3_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory704 (x_2_5 x_3_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory705 (x_1_6 x_1_8 x_3_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory706 (x_3_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory707 (x_0_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory708 (x_0_2 x_2_7 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory709 (x_1_9 x_3_9 x_9_10 : ℝ) : (¬ ((x_1_9 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory710 (x_1_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory712 (x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory713 (x_3_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) ∨ ((x_5_6 + ((-1) * x_6_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

end ElevenTheory
