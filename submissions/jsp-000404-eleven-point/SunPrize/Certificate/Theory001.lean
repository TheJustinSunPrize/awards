import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory204 (t x_3_4 x_3_8 x_4_8 : ℝ) : ((((x_3_4 ≤ x_3_8) ∧ (x_3_8 ≤ x_4_8) ∧ ((x_4_8 - x_3_4) ≥ 1) ∧ ((x_3_8 - x_3_4) ≤ (t - 1)) ∧ ((x_4_8 - x_3_8) ≤ (t - 1))) ∨ ((x_4_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_4) ∧ ((x_3_4 - x_4_8) ≥ 1) ∧ ((x_3_4 - x_3_8) ≤ (t - 1)) ∧ ((x_3_8 - x_4_8) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_8) ∧ (x_3_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_4_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_4 ≤ x_3_8) ↔ (((1) * x_3_4 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_8 ≤ x_4_8) ↔ (((1) * x_3_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_8 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_8 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_4_8) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_4 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory205 (t x_0_1 x_0_6 x_1_6 : ℝ) : ((((x_0_1 ≤ x_0_6) ∧ (x_0_6 ≤ x_1_6) ∧ ((x_1_6 - x_0_1) ≥ 1) ∧ ((x_0_6 - x_0_1) ≤ (t - 1)) ∧ ((x_1_6 - x_0_6) ≤ (t - 1))) ∨ ((x_1_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_1) ∧ ((x_0_1 - x_1_6) ≥ 1) ∧ ((x_0_1 - x_0_6) ≤ (t - 1)) ∧ ((x_0_6 - x_1_6) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_6) ∧ (x_0_6 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_1_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_1_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_1 ≤ x_0_6) ↔ (((1) * x_0_1 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_6 ≤ x_1_6) ↔ (((1) * x_0_6 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_6 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_6 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_1_6) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_1 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_6 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory206 (x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_5_6)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory207 (t x_2_5 x_2_9 x_5_9 : ℝ) : ((((x_2_5 ≤ x_2_9) ∧ (x_2_9 ≤ x_5_9) ∧ ((x_5_9 - x_2_5) ≥ 1) ∧ ((x_2_9 - x_2_5) ≤ (t - 1)) ∧ ((x_5_9 - x_2_9) ≤ (t - 1))) ∨ ((x_5_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_5) ∧ ((x_2_5 - x_5_9) ≥ 1) ∧ ((x_2_5 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_5_9) ≤ (t - 1)))) ↔ (((x_2_5 ≤ x_2_9) ∧ (x_2_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_5_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_5 ≤ x_2_9) ↔ (((1) * x_2_5 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_9 ≤ x_5_9) ↔ (((1) * x_2_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_9 - x_2_5) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_9 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_5 - x_5_9) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_5 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory208 (t x_3_5 x_3_9 x_5_9 : ℝ) : ((((x_3_5 ≤ x_3_9) ∧ (x_3_9 ≤ x_5_9) ∧ ((x_5_9 - x_3_5) ≥ 1) ∧ ((x_3_9 - x_3_5) ≤ (t - 1)) ∧ ((x_5_9 - x_3_9) ≤ (t - 1))) ∨ ((x_5_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_5) ∧ ((x_3_5 - x_5_9) ≥ 1) ∧ ((x_3_5 - x_3_9) ≤ (t - 1)) ∧ ((x_3_9 - x_5_9) ≤ (t - 1)))) ↔ (((x_3_5 ≤ x_3_9) ∧ (x_3_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_5_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_5 ≤ x_3_9) ↔ (((1) * x_3_5 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_9 ≤ x_5_9) ↔ (((1) * x_3_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_9 - x_3_5) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_9 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_5 - x_5_9) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_5 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory209 (t x_5_6 x_5_9 x_6_9 : ℝ) : ((((x_5_6 ≤ x_5_9) ∧ (x_5_9 ≤ x_6_9) ∧ ((x_6_9 - x_5_6) ≥ 1) ∧ ((x_5_9 - x_5_6) ≤ (t - 1)) ∧ ((x_6_9 - x_5_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_6) ∧ ((x_5_6 - x_6_9) ≥ 1) ∧ ((x_5_6 - x_5_9) ≤ (t - 1)) ∧ ((x_5_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_5_6 ≤ x_5_9) ∧ (x_5_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_5_6 ≤ x_5_9) ↔ (((1) * x_5_6 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_9 ≤ x_6_9) ↔ (((1) * x_5_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_9 - x_5_6) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_9 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_9 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_6 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_6_9 + (-1)) < 0)) := by
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
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory210 (t x_6_9 : ℝ) : ((¬ (t ≤ x_6_9)) ↔ (¬ ((t + ((-1) * x_6_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_6_9) ↔ (((1) * t + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * t + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory211 (t x_2_3 x_2_5 x_3_5 : ℝ) : ((((x_2_3 ≤ x_2_5) ∧ (x_2_5 ≤ x_3_5) ∧ ((x_3_5 - x_2_3) ≥ 1) ∧ ((x_2_5 - x_2_3) ≤ (t - 1)) ∧ ((x_3_5 - x_2_5) ≤ (t - 1))) ∨ ((x_3_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_3) ∧ ((x_2_3 - x_3_5) ≥ 1) ∧ ((x_2_3 - x_2_5) ≤ (t - 1)) ∧ ((x_2_5 - x_3_5) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_5) ∧ (x_2_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_2_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_3_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_3 ≤ x_2_5) ↔ (((1) * x_2_3 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_5 ≤ x_3_5) ↔ (((1) * x_2_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_5 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_5 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_5 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_5 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_5 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_3_5) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_5 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_5 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory212 (t x_5_8 x_5_9 x_8_9 : ℝ) : ((((x_5_8 ≤ x_5_9) ∧ (x_5_9 ≤ x_8_9) ∧ ((x_8_9 - x_5_8) ≥ 1) ∧ ((x_5_9 - x_5_8) ≤ (t - 1)) ∧ ((x_8_9 - x_5_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_8) ∧ ((x_5_8 - x_8_9) ≥ 1) ∧ ((x_5_8 - x_5_9) ≤ (t - 1)) ∧ ((x_5_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_5_8 ≤ x_5_9) ∧ (x_5_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_8 ≤ x_5_9) ↔ (((1) * x_5_8 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_9 ≤ x_8_9) ↔ (((1) * x_5_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_5_8) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_9 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_5_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_5_8)) ≥ 1) ↔ (((1) * x_5_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_8 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory213 (t x_3_5 x_3_8 x_5_8 : ℝ) : ((((x_3_5 ≤ x_3_8) ∧ (x_3_8 ≤ x_5_8) ∧ ((x_5_8 - x_3_5) ≥ 1) ∧ ((x_3_8 - x_3_5) ≤ (t - 1)) ∧ ((x_5_8 - x_3_8) ≤ (t - 1))) ∨ ((x_5_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_5) ∧ ((x_3_5 - x_5_8) ≥ 1) ∧ ((x_3_5 - x_3_8) ≤ (t - 1)) ∧ ((x_3_8 - x_5_8) ≤ (t - 1)))) ↔ (((x_3_5 ≤ x_3_8) ∧ (x_3_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_5_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_5 ≤ x_3_8) ↔ (((1) * x_3_5 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_5_8) ↔ (((1) * x_3_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_8 - x_3_5) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_8 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_8 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_5 - x_5_8) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_5 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory214 (t x_0_3 x_0_8 x_3_8 : ℝ) : ((((x_0_3 ≤ x_0_8) ∧ (x_0_8 ≤ x_3_8) ∧ ((x_3_8 - x_0_3) ≥ 1) ∧ ((x_0_8 - x_0_3) ≤ (t - 1)) ∧ ((x_3_8 - x_0_8) ≤ (t - 1))) ∨ ((x_3_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_3) ∧ ((x_0_3 - x_3_8) ≥ 1) ∧ ((x_0_3 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_3_8) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_8) ∧ (x_0_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_3_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_3 ≤ x_0_8) ↔ (((1) * x_0_3 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_8 ≤ x_3_8) ↔ (((1) * x_0_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_8 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_3 - x_3_8) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_8 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory215 (t x_0_3 x_0_8 x_3_8 : ℝ) : ((((x_0_3 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_3_8)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_3_8)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_3 + ((-1) * x_0_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((t + x_0_8 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1)))))) := by
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
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory216 (t x_0_3 x_0_8 x_3_8 : ℝ) : ((((x_0_8 + ((-1) * x_3_8)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_3_8) ≥ 1)) ↔ (¬ ((¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_8) + x_3_8) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_8) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_8 + ((-1) * x_3_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_3 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_3) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_8) + x_3_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory217 (t x_1_3 x_1_8 x_3_8 : ℝ) : ((((x_1_3 ≤ x_1_8) ∧ (x_1_8 ≤ x_3_8) ∧ ((x_3_8 - x_1_3) ≥ 1) ∧ ((x_1_8 - x_1_3) ≤ (t - 1)) ∧ ((x_3_8 - x_1_8) ≤ (t - 1))) ∨ ((x_3_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_3) ∧ ((x_1_3 - x_3_8) ≥ 1) ∧ ((x_1_3 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_3_8) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_8) ∧ (x_1_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_3_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_3 ≤ x_1_8) ↔ (((1) * x_1_3 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_3_8) ↔ (((1) * x_1_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_8 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_3 - x_3_8) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory218 (x_1_4 x_4_7 x_4_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory219 (t x_2_4 x_2_7 x_4_7 : ℝ) : ((((x_2_4 ≤ x_2_7) ∧ (x_2_7 ≤ x_4_7) ∧ ((x_4_7 - x_2_4) ≥ 1) ∧ ((x_2_7 - x_2_4) ≤ (t - 1)) ∧ ((x_4_7 - x_2_7) ≤ (t - 1))) ∨ ((x_4_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_4) ∧ ((x_2_4 - x_4_7) ≥ 1) ∧ ((x_2_4 - x_2_7) ≤ (t - 1)) ∧ ((x_2_7 - x_4_7) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_7) ∧ (x_2_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_4_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_4 ≤ x_2_7) ↔ (((1) * x_2_4 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_7 ≤ x_4_7) ↔ (((1) * x_2_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_7 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_7 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_7 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_4_7) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_4 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory221 (t x_0_5 x_0_9 x_5_9 : ℝ) : ((((x_0_5 ≤ x_0_9) ∧ (x_0_9 ≤ x_5_9) ∧ ((x_5_9 - x_0_5) ≥ 1) ∧ ((x_0_9 - x_0_5) ≤ (t - 1)) ∧ ((x_5_9 - x_0_9) ≤ (t - 1))) ∨ ((x_5_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_5) ∧ ((x_0_5 - x_5_9) ≥ 1) ∧ ((x_0_5 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_5_9) ≤ (t - 1)))) ↔ (((x_0_5 ≤ x_0_9) ∧ (x_0_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_5_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_5 ≤ x_0_9) ↔ (((1) * x_0_5 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_9 ≤ x_5_9) ↔ (((1) * x_0_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_9 - x_0_5) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_9 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_5 - x_5_9) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_5 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_9 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory222 (t x_1_4 x_1_9 x_4_9 : ℝ) : ((((x_1_4 ≤ x_1_9) ∧ (x_1_9 ≤ x_4_9) ∧ ((x_4_9 - x_1_4) ≥ 1) ∧ ((x_1_9 - x_1_4) ≤ (t - 1)) ∧ ((x_4_9 - x_1_9) ≤ (t - 1))) ∨ ((x_4_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_4) ∧ ((x_1_4 - x_4_9) ≥ 1) ∧ ((x_1_4 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_4_9) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_9) ∧ (x_1_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_4_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_4 ≤ x_1_9) ↔ (((1) * x_1_4 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_9 ≤ x_4_9) ↔ (((1) * x_1_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_9 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_4 - x_4_9) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_9 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory223 (t x_1_4 x_1_9 x_4_9 : ℝ) : ((((x_1_4 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_4_9)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_4 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((t + x_1_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_9)) ≤ 0))))) := by
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
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory224 (t x_1_4 x_1_9 x_4_9 : ℝ) : ((((x_1_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_4_9) ≥ 1)) ↔ (¬ ((¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_9) + x_4_9) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_9)) ≥ 0))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory225 (x_1_4 x_4_5 x_4_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory226 (x_1_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory227 (t x_5_7 x_5_9 x_7_9 : ℝ) : ((((x_5_7 ≤ x_5_9) ∧ (x_5_9 ≤ x_7_9) ∧ ((x_7_9 - x_5_7) ≥ 1) ∧ ((x_5_9 - x_5_7) ≤ (t - 1)) ∧ ((x_7_9 - x_5_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_7) ∧ ((x_5_7 - x_7_9) ≥ 1) ∧ ((x_5_7 - x_5_9) ≤ (t - 1)) ∧ ((x_5_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_5_7 ≤ x_5_9) ∧ (x_5_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_5_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_5_9) ∧ (x_5_9 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_7 ≤ x_5_9) ↔ (((1) * x_5_7 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_9 ≤ x_7_9) ↔ (((1) * x_5_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_5_7) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_9 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_5_9) ↔ (¬ (((1) * x_5_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_9 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_5_7)) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_9 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_7 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory228 (t x_3_8 x_3_9 x_8_9 : ℝ) : ((((x_3_8 ≤ x_3_9) ∧ (x_3_9 ≤ x_8_9) ∧ ((x_8_9 - x_3_8) ≥ 1) ∧ ((x_3_9 - x_3_8) ≤ (t - 1)) ∧ ((x_8_9 - x_3_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_8) ∧ ((x_3_8 - x_8_9) ≥ 1) ∧ ((x_3_8 - x_3_9) ≤ (t - 1)) ∧ ((x_3_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_3_8 ≤ x_3_9) ∧ (x_3_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_3_9) ↔ (((1) * x_3_8 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_9 ≤ x_8_9) ↔ (((1) * x_3_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_3_8) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_9 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_3_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_3_8)) ≥ 1) ↔ (((1) * x_3_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_9 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_8 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory229 (t x_8_10 x_8_9 x_9_10 : ℝ) : ((((x_8_9 ≤ x_8_10) ∧ (x_8_10 ≤ x_9_10) ∧ ((x_9_10 - x_8_9) ≥ 1) ∧ ((x_8_10 - x_8_9) ≤ (t - 1)) ∧ ((x_9_10 - x_8_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_8_10) ∧ (x_8_10 ≤ x_8_9) ∧ ((x_8_9 - x_9_10) ≥ 1) ∧ ((x_8_9 - x_8_10) ≤ (t - 1)) ∧ ((x_8_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_8_9 ≤ x_8_10) ∧ (x_8_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_8_10 + ((-1) * x_8_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_8_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_8_10) ∧ (x_8_10 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_8_9 + ((-1) * x_8_10)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_8_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_8_9 ≤ x_8_10) ↔ (¬ (((1) * x_8_10 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_8_10 ≤ x_9_10) ↔ (((1) * x_8_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_9_10 - x_8_9) ≥ 1) ↔ (((1) * x_8_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_10 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_9_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_9_10 ≤ x_8_10) ↔ (¬ (((1) * x_8_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_10 ≤ x_8_9) ↔ (((1) * x_8_10 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_8_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_8_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_9 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_8_9)) ≥ 1) ↔ (((1) * x_8_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_10 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_9_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_8_9 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_8_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory230 (t x_4_10 x_4_9 x_9_10 : ℝ) : ((((x_4_9 ≤ x_4_10) ∧ (x_4_10 ≤ x_9_10) ∧ ((x_9_10 - x_4_9) ≥ 1) ∧ ((x_4_10 - x_4_9) ≤ (t - 1)) ∧ ((x_9_10 - x_4_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_9) ∧ ((x_4_9 - x_9_10) ≥ 1) ∧ ((x_4_9 - x_4_10) ≤ (t - 1)) ∧ ((x_4_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_4_9 ≤ x_4_10) ∧ (x_4_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_4_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_9 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_10 ≤ x_9_10) ↔ (((1) * x_4_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_9_10 - x_4_9) ≥ 1) ↔ (((1) * x_4_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_10 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_9_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_9_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_4_9) ↔ (((1) * x_4_10 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_4_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_9 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_4_9)) ≥ 1) ↔ (((1) * x_4_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_10 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_9_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_9 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory231 (t x_0_3 x_0_9 x_3_9 : ℝ) : ((((x_0_3 ≤ x_0_9) ∧ (x_0_9 ≤ x_3_9) ∧ ((x_3_9 - x_0_3) ≥ 1) ∧ ((x_0_9 - x_0_3) ≤ (t - 1)) ∧ ((x_3_9 - x_0_9) ≤ (t - 1))) ∨ ((x_3_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_3) ∧ ((x_0_3 - x_3_9) ≥ 1) ∧ ((x_0_3 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_3_9) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_9) ∧ (x_0_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_3_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_3 ≤ x_0_9) ↔ (((1) * x_0_3 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_9 ≤ x_3_9) ↔ (((1) * x_0_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_9 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_9 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_3 - x_3_9) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_9 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory232 (t x_0_3 x_0_9 x_3_9 : ℝ) : ((((x_0_3 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_3_9)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((t + x_0_3 + ((-1) * x_0_9)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_9)) ≤ 0))))) := by
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
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory233 (t x_0_3 x_0_9 x_3_9 : ℝ) : ((((x_0_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_3_9) ≥ 1)) ↔ (¬ ((¬ ((x_0_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_9) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_9) + x_3_9) ≥ 1))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_9 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_3 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_3) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_9) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory234 (t x_1_6 x_1_7 x_6_7 : ℝ) : ((((x_1_6 ≤ x_1_7) ∧ (x_1_7 ≤ x_6_7) ∧ ((x_6_7 - x_1_6) ≥ 1) ∧ ((x_1_7 - x_1_6) ≤ (t - 1)) ∧ ((x_6_7 - x_1_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_6) ∧ ((x_1_6 - x_6_7) ≥ 1) ∧ ((x_1_6 - x_1_7) ≤ (t - 1)) ∧ ((x_1_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_1_6 ≤ x_1_7) ∧ (x_1_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_6 ≤ x_1_7) ↔ (((1) * x_1_6 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_7 ≤ x_6_7) ↔ (((1) * x_1_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_1_6) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_7 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_7 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_6 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_7 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory235 (t x_1_6 x_1_9 x_6_9 : ℝ) : ((((x_1_6 ≤ x_1_9) ∧ (x_1_9 ≤ x_6_9) ∧ ((x_6_9 - x_1_6) ≥ 1) ∧ ((x_1_9 - x_1_6) ≤ (t - 1)) ∧ ((x_6_9 - x_1_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_6) ∧ ((x_1_6 - x_6_9) ≥ 1) ∧ ((x_1_6 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_1_6 ≤ x_1_9) ∧ (x_1_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_6 ≤ x_1_9) ↔ (((1) * x_1_6 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_9 ≤ x_6_9) ↔ (((1) * x_1_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_1_6) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_9 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_6 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory236 (x_3_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory237 (x_1_6 x_6_7 x_6_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((x_1_6 + ((-1) * x_6_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory238 (t x_2_4 x_2_9 x_4_9 : ℝ) : ((((x_2_4 ≤ x_2_9) ∧ (x_2_9 ≤ x_4_9) ∧ ((x_4_9 - x_2_4) ≥ 1) ∧ ((x_2_9 - x_2_4) ≤ (t - 1)) ∧ ((x_4_9 - x_2_9) ≤ (t - 1))) ∨ ((x_4_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_4) ∧ ((x_2_4 - x_4_9) ≥ 1) ∧ ((x_2_4 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_4_9) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_9) ∧ (x_2_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_4_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_4 ≤ x_2_9) ↔ (((1) * x_2_4 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_9 ≤ x_4_9) ↔ (((1) * x_2_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_9 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 - x_4_9) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory239 (t x_3_4 x_3_9 x_4_9 : ℝ) : ((((x_3_4 ≤ x_3_9) ∧ (x_3_9 ≤ x_4_9) ∧ ((x_4_9 - x_3_4) ≥ 1) ∧ ((x_3_9 - x_3_4) ≤ (t - 1)) ∧ ((x_4_9 - x_3_9) ≤ (t - 1))) ∨ ((x_4_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_4) ∧ ((x_3_4 - x_4_9) ≥ 1) ∧ ((x_3_4 - x_3_9) ≤ (t - 1)) ∧ ((x_3_9 - x_4_9) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_9) ∧ (x_3_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_4_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_4 ≤ x_3_9) ↔ (((1) * x_3_4 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_9 ≤ x_4_9) ↔ (((1) * x_3_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_9 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_4 - x_4_9) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory240 (x_0_4 x_1_4 x_4_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory241 (t x_0_4 x_0_9 x_4_9 : ℝ) : ((((x_0_4 ≤ x_0_9) ∧ (x_0_9 ≤ x_4_9) ∧ ((x_4_9 - x_0_4) ≥ 1) ∧ ((x_0_9 - x_0_4) ≤ (t - 1)) ∧ ((x_4_9 - x_0_9) ≤ (t - 1))) ∨ ((x_4_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_4) ∧ ((x_0_4 - x_4_9) ≥ 1) ∧ ((x_0_4 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_4_9) ≤ (t - 1)))) ↔ (((x_0_4 ≤ x_0_9) ∧ (x_0_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_4_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_4 ≤ x_0_9) ↔ (((1) * x_0_4 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_9 ≤ x_4_9) ↔ (((1) * x_0_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 - x_0_4) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_9 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_4 - x_4_9) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_4 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_9 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory242 (x_3_4 x_4_8 x_4_9 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory243 (t x_0_7 : ℝ) : ((¬ (t ≤ x_0_7)) ↔ (¬ ((t + ((-1) * x_0_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_7) ↔ (((1) * t + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * t + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory244 (x_0_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory245 (x_0_2 x_0_4 x_2_3 x_2_4 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory246 (x_0_2 x_1_2 x_2_4 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory247 (x_0_1 x_1_3 x_1_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory248 (x_0_2 x_1_2 x_2_3 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory249 (x_0_1 x_0_5 x_1_2 x_1_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory250 (t x_0_1 x_0_4 x_1_4 : ℝ) : ((((x_0_1 ≤ x_0_4) ∧ (x_0_4 ≤ x_1_4) ∧ ((x_1_4 - x_0_1) ≥ 1) ∧ ((x_0_4 - x_0_1) ≤ (t - 1)) ∧ ((x_1_4 - x_0_4) ≤ (t - 1))) ∨ ((x_1_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_1) ∧ ((x_0_1 - x_1_4) ≥ 1) ∧ ((x_0_1 - x_0_4) ≤ (t - 1)) ∧ ((x_0_4 - x_1_4) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_4) ∧ (x_0_4 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_1_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_1_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_1 ≤ x_0_4) ↔ (((1) * x_0_1 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_4 ≤ x_1_4) ↔ (((1) * x_0_4 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_4 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_4 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_4 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_4 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_1_4) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_1 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_4 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_4 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_4 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory251 (t x_0_4 x_0_7 x_4_7 : ℝ) : ((((x_0_4 ≤ x_0_7) ∧ (x_0_7 ≤ x_4_7) ∧ ((x_4_7 - x_0_4) ≥ 1) ∧ ((x_0_7 - x_0_4) ≤ (t - 1)) ∧ ((x_4_7 - x_0_7) ≤ (t - 1))) ∨ ((x_4_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_4) ∧ ((x_0_4 - x_4_7) ≥ 1) ∧ ((x_0_4 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_4_7) ≤ (t - 1)))) ↔ (((x_0_4 ≤ x_0_7) ∧ (x_0_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_4_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_0_7) ↔ (((1) * x_0_4 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_7 ≤ x_4_7) ↔ (((1) * x_0_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_7 - x_0_4) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_7 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_4 - x_4_7) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory252 (t x_0_1 x_0_7 x_1_7 : ℝ) : ((((x_0_1 ≤ x_0_7) ∧ (x_0_7 ≤ x_1_7) ∧ ((x_1_7 - x_0_1) ≥ 1) ∧ ((x_0_7 - x_0_1) ≤ (t - 1)) ∧ ((x_1_7 - x_0_7) ≤ (t - 1))) ∨ ((x_1_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_1) ∧ ((x_0_1 - x_1_7) ≥ 1) ∧ ((x_0_1 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_1_7) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_7) ∧ (x_0_7 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_1_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_1_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_1 ≤ x_0_7) ↔ (((1) * x_0_1 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_7 ≤ x_1_7) ↔ (((1) * x_0_7 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_7 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_1 - x_1_7) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_7 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory253 (x_0_1 x_1_3 x_1_4 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory254 (t x_1_2 x_1_4 x_2_4 : ℝ) : ((((x_1_2 ≤ x_1_4) ∧ (x_1_4 ≤ x_2_4) ∧ ((x_2_4 - x_1_2) ≥ 1) ∧ ((x_1_4 - x_1_2) ≤ (t - 1)) ∧ ((x_2_4 - x_1_4) ≤ (t - 1))) ∨ ((x_2_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_2) ∧ ((x_1_2 - x_2_4) ≥ 1) ∧ ((x_1_2 - x_1_4) ≤ (t - 1)) ∧ ((x_1_4 - x_2_4) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_4) ∧ (x_1_4 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_1_4)) ≤ ((-1) + t))) ∨ ((x_2_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_2_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_2 ≤ x_1_4) ↔ (((1) * x_1_2 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_4 ≤ x_2_4) ↔ (((1) * x_1_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_4 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_4 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_4 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_4 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_4 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_2_4) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_2 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_4 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_4 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory255 (x_1_3 x_1_5 x_3_4 x_3_5 : ℝ) : (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory256 (x_0_3 x_2_3 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory257 (t x_2_4 x_2_6 x_4_6 : ℝ) : ((((x_2_4 ≤ x_2_6) ∧ (x_2_6 ≤ x_4_6) ∧ ((x_4_6 - x_2_4) ≥ 1) ∧ ((x_2_6 - x_2_4) ≤ (t - 1)) ∧ ((x_4_6 - x_2_6) ≤ (t - 1))) ∨ ((x_4_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_4) ∧ ((x_2_4 - x_4_6) ≥ 1) ∧ ((x_2_4 - x_2_6) ≤ (t - 1)) ∧ ((x_2_6 - x_4_6) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_6) ∧ (x_2_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_4_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_4 ≤ x_2_6) ↔ (((1) * x_2_4 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_6 ≤ x_4_6) ↔ (((1) * x_2_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_6 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_6 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 - x_4_6) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_6 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_6 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory258 (x_0_3 x_2_3 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory259 (x_0_2 x_2_6 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory260 (t x_2_7 x_2_9 x_7_9 : ℝ) : ((((x_2_7 ≤ x_2_9) ∧ (x_2_9 ≤ x_7_9) ∧ ((x_7_9 - x_2_7) ≥ 1) ∧ ((x_2_9 - x_2_7) ≤ (t - 1)) ∧ ((x_7_9 - x_2_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_7) ∧ ((x_2_7 - x_7_9) ≥ 1) ∧ ((x_2_7 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_2_7 ≤ x_2_9) ∧ (x_2_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_7 ≤ x_2_9) ↔ (((1) * x_2_7 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_9 ≤ x_7_9) ↔ (((1) * x_2_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_9 - x_2_7) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_9 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_7 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_9 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_7 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory261 (t x_2_7 : ℝ) : ((¬ (t ≤ x_2_7)) ↔ (¬ ((t + ((-1) * x_2_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_7) ↔ (((1) * t + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * t + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory262 (x_0_8 x_1_8 x_1_9 x_8_9 : ℝ) : (¬ ((x_1_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_1_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory263 (t x_1_8 : ℝ) : ((¬ (t ≤ x_1_8)) ↔ (¬ ((t + ((-1) * x_1_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_8) ↔ (((1) * t + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * t + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory264 (t x_0_1 x_0_8 x_1_8 : ℝ) : ((((x_0_1 ≤ x_0_8) ∧ (x_0_8 ≤ x_1_8) ∧ ((x_1_8 - x_0_1) ≥ 1) ∧ ((x_0_8 - x_0_1) ≤ (t - 1)) ∧ ((x_1_8 - x_0_8) ≤ (t - 1))) ∨ ((x_1_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_1) ∧ ((x_0_1 - x_1_8) ≥ 1) ∧ ((x_0_1 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_1_8) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_8) ∧ (x_0_8 ≤ x_1_8) ∧ ((x_1_8 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_1_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_1_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_1 ≤ x_0_8) ↔ (((1) * x_0_1 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_8 ≤ x_1_8) ↔ (((1) * x_0_8 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_8 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_1 - x_1_8) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_8 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory265 (x_0_1 x_1_4 x_1_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory266 (t x_6_10 x_6_9 x_9_10 : ℝ) : ((((x_6_9 ≤ x_6_10) ∧ (x_6_10 ≤ x_9_10) ∧ ((x_9_10 - x_6_9) ≥ 1) ∧ ((x_6_10 - x_6_9) ≤ (t - 1)) ∧ ((x_9_10 - x_6_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_9) ∧ ((x_6_9 - x_9_10) ≥ 1) ∧ ((x_6_9 - x_6_10) ≤ (t - 1)) ∧ ((x_6_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_6_9 ≤ x_6_10) ∧ (x_6_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_6_9 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_10 ≤ x_9_10) ↔ (((1) * x_6_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_9_10 - x_6_9) ≥ 1) ↔ (((1) * x_6_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_9_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_9_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_6_9) ↔ (((1) * x_6_10 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_6_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_6_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_9 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_9_10 + ((-1) * x_6_9)) ≥ 1) ↔ (((1) * x_6_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_9_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_6_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_9 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory267 (t x_0_2 x_0_7 x_2_7 : ℝ) : ((((x_0_2 ≤ x_0_7) ∧ (x_0_7 ≤ x_2_7) ∧ ((x_2_7 - x_0_2) ≥ 1) ∧ ((x_0_7 - x_0_2) ≤ (t - 1)) ∧ ((x_2_7 - x_0_7) ≤ (t - 1))) ∨ ((x_2_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_2) ∧ ((x_0_2 - x_2_7) ≥ 1) ∧ ((x_0_2 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_2_7) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_7) ∧ (x_0_7 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_2_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_2_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_2 ≤ x_0_7) ↔ (((1) * x_0_2 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_7 ≤ x_2_7) ↔ (((1) * x_0_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_7 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_7 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 - x_2_7) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_7 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory268 (t x_2_5 : ℝ) : ((¬ (t ≤ x_2_5)) ↔ (¬ ((t + ((-1) * x_2_5)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_5) ↔ (((1) * t + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * t + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory269 (x_0_2 x_2_3 x_2_4 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory270 (x_0_3 x_2_3 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory271 (x_0_3 x_2_3 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory272 (t x_2_6 x_2_9 x_6_9 : ℝ) : ((((x_2_6 ≤ x_2_9) ∧ (x_2_9 ≤ x_6_9) ∧ ((x_6_9 - x_2_6) ≥ 1) ∧ ((x_2_9 - x_2_6) ≤ (t - 1)) ∧ ((x_6_9 - x_2_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_6) ∧ ((x_2_6 - x_6_9) ≥ 1) ∧ ((x_2_6 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_2_6 ≤ x_2_9) ∧ (x_2_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_6 ≤ x_2_9) ↔ (((1) * x_2_6 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_9 ≤ x_6_9) ↔ (((1) * x_2_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_2_6) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_9 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_9 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_9 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory273 (x_0_5 x_1_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory274 (x_1_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory275 (t x_3_6 x_3_9 x_6_9 : ℝ) : ((((x_3_6 ≤ x_3_9) ∧ (x_3_9 ≤ x_6_9) ∧ ((x_6_9 - x_3_6) ≥ 1) ∧ ((x_3_9 - x_3_6) ≤ (t - 1)) ∧ ((x_6_9 - x_3_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_6) ∧ ((x_3_6 - x_6_9) ≥ 1) ∧ ((x_3_6 - x_3_9) ≤ (t - 1)) ∧ ((x_3_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_3_6 ≤ x_3_9) ∧ (x_3_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_3_9) ↔ (((1) * x_3_6 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_9 ≤ x_6_9) ↔ (((1) * x_3_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_3_6) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_9 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_9 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory276 (x_1_4 x_3_4 x_4_7 : ℝ) : (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory277 (x_3_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory278 (t x_4_8 : ℝ) : ((¬ (t ≤ x_4_8)) ↔ (¬ ((t + ((-1) * x_4_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_4_8) ↔ (((1) * t + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * t + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory279 (t x_3_10 x_3_9 x_9_10 : ℝ) : ((((x_3_9 ≤ x_3_10) ∧ (x_3_10 ≤ x_9_10) ∧ ((x_9_10 - x_3_9) ≥ 1) ∧ ((x_3_10 - x_3_9) ≤ (t - 1)) ∧ ((x_9_10 - x_3_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_9) ∧ ((x_3_9 - x_9_10) ≥ 1) ∧ ((x_3_9 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_3_9 ≤ x_3_10) ∧ (x_3_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_3_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_9 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_10 ≤ x_9_10) ↔ (((1) * x_3_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_9_10 - x_3_9) ≥ 1) ↔ (((1) * x_3_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_10 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_9_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_9_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_3_9) ↔ (((1) * x_3_10 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_3_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_3_9)) ≥ 1) ↔ (((1) * x_3_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_10 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_9_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_9 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory280 (t x_0_7 x_0_9 x_7_9 : ℝ) : ((((x_0_7 ≤ x_0_9) ∧ (x_0_9 ≤ x_7_9) ∧ ((x_7_9 - x_0_7) ≥ 1) ∧ ((x_0_9 - x_0_7) ≤ (t - 1)) ∧ ((x_7_9 - x_0_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_7) ∧ ((x_0_7 - x_7_9) ≥ 1) ∧ ((x_0_7 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_0_7 ≤ x_0_9) ∧ (x_0_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_7 ≤ x_0_9) ↔ (((1) * x_0_7 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_9 ≤ x_7_9) ↔ (((1) * x_0_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_0_7) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_9 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_9 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_7 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_9 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory281 (x_0_4 x_1_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory282 (t x_1_7 x_1_8 x_7_8 : ℝ) : ((((x_1_7 ≤ x_1_8) ∧ (x_1_8 ≤ x_7_8) ∧ ((x_7_8 - x_1_7) ≥ 1) ∧ ((x_1_8 - x_1_7) ≤ (t - 1)) ∧ ((x_7_8 - x_1_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_7) ∧ ((x_1_7 - x_7_8) ≥ 1) ∧ ((x_1_7 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_1_7 ≤ x_1_8) ∧ (x_1_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_1_8) ↔ (((1) * x_1_7 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_8 ≤ x_7_8) ↔ (((1) * x_1_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 - x_1_7) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_8 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_8 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_8 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory283 (t x_1_2 x_1_8 x_2_8 : ℝ) : ((((x_1_2 ≤ x_1_8) ∧ (x_1_8 ≤ x_2_8) ∧ ((x_2_8 - x_1_2) ≥ 1) ∧ ((x_1_8 - x_1_2) ≤ (t - 1)) ∧ ((x_2_8 - x_1_8) ≤ (t - 1))) ∨ ((x_2_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_2) ∧ ((x_1_2 - x_2_8) ≥ 1) ∧ ((x_1_2 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_2_8) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_8) ∧ (x_1_8 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_2_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_2_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_2 ≤ x_1_8) ↔ (((1) * x_1_2 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_8 ≤ x_2_8) ↔ (((1) * x_1_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_8 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_8 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_8 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_2_8) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_2 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_8 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory284 (x_0_4 x_1_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory285 (x_0_1 x_1_2 x_1_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory286 (x_0_7 x_1_7 x_1_8 x_7_8 : ℝ) : (¬ ((x_1_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory288 (x_1_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory289 (x_1_6 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory291 (x_0_6 x_0_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory292 (x_3_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory293 (x_0_1 x_1_5 x_1_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory294 (x_0_5 x_3_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory295 (x_0_3 x_0_5 x_3_5 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory296 (x_0_4 x_1_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory297 (t x_4_6 x_4_9 x_6_9 : ℝ) : ((((x_4_6 ≤ x_4_9) ∧ (x_4_9 ≤ x_6_9) ∧ ((x_6_9 - x_4_6) ≥ 1) ∧ ((x_4_9 - x_4_6) ≤ (t - 1)) ∧ ((x_6_9 - x_4_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_6) ∧ ((x_4_6 - x_6_9) ≥ 1) ∧ ((x_4_6 - x_4_9) ≤ (t - 1)) ∧ ((x_4_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_4_6 ≤ x_4_9) ∧ (x_4_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_6 ≤ x_4_9) ↔ (((1) * x_4_6 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_9 ≤ x_6_9) ↔ (((1) * x_4_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_4_6) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_6 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory298 (x_0_6 x_0_7 x_3_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory299 (x_0_7 x_6_7 : ℝ) : ((x_0_7 + ((-1) * x_6_7)) ≥ 0) ∨ ((x_0_7 + ((-1) * x_6_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory301 (x_1_7 x_4_7 x_5_7 : ℝ) : (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_1_7 + ((-1) * x_5_7)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory302 (x_1_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory303 (x_0_3 x_2_3 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory304 (x_0_4 x_3_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory307 (t x_5_8 : ℝ) : ((¬ (t ≤ x_5_8)) ↔ (¬ ((t + ((-1) * x_5_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_5_8) ↔ (((1) * t + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_5_8)) ≤ 0) ↔ (((1) * t + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory308 (x_3_4 x_3_7 x_4_6 x_4_7 : ℝ) : (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory309 (x_1_2 x_2_4 x_2_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory310 (x_2_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory311 (x_0_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory312 (x_0_2 x_1_2 x_2_4 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory313 (t x_2_6 : ℝ) : ((¬ (t ≤ x_2_6)) ↔ (¬ ((t + ((-1) * x_2_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_6) ↔ (((1) * t + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * t + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory314 (x_0_6 x_3_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory315 (x_1_2 x_2_5 x_2_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory316 (x_1_4 x_1_6 x_4_5 x_4_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory317 (x_0_4 x_1_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory319 (t x_1_2 x_1_9 x_2_9 : ℝ) : ((((x_1_2 ≤ x_1_9) ∧ (x_1_9 ≤ x_2_9) ∧ ((x_2_9 - x_1_2) ≥ 1) ∧ ((x_1_9 - x_1_2) ≤ (t - 1)) ∧ ((x_2_9 - x_1_9) ≤ (t - 1))) ∨ ((x_2_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_2) ∧ ((x_1_2 - x_2_9) ≥ 1) ∧ ((x_1_2 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_2_9) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_9) ∧ (x_1_9 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_2_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_2_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_2 ≤ x_1_9) ↔ (((1) * x_1_2 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_9 ≤ x_2_9) ↔ (((1) * x_1_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_9 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_9 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 - x_2_9) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_9 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory320 (t x_2_8 x_2_9 x_8_9 : ℝ) : ((((x_2_8 ≤ x_2_9) ∧ (x_2_9 ≤ x_8_9) ∧ ((x_8_9 - x_2_8) ≥ 1) ∧ ((x_2_9 - x_2_8) ≤ (t - 1)) ∧ ((x_8_9 - x_2_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_8) ∧ ((x_2_8 - x_8_9) ≥ 1) ∧ ((x_2_8 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_2_8 ≤ x_2_9) ∧ (x_2_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_8 ≤ x_2_9) ↔ (((1) * x_2_8 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_9 ≤ x_8_9) ↔ (((1) * x_2_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_2_8) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_9 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_9 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_2_8)) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_9 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory321 (t x_0_2 x_0_9 x_2_9 : ℝ) : ((((x_0_2 ≤ x_0_9) ∧ (x_0_9 ≤ x_2_9) ∧ ((x_2_9 - x_0_2) ≥ 1) ∧ ((x_0_9 - x_0_2) ≤ (t - 1)) ∧ ((x_2_9 - x_0_9) ≤ (t - 1))) ∨ ((x_2_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_2) ∧ ((x_0_2 - x_2_9) ≥ 1) ∧ ((x_0_2 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_2_9) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_9) ∧ (x_0_9 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_2_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_2_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_2 ≤ x_0_9) ↔ (((1) * x_0_2 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_9 ≤ x_2_9) ↔ (((1) * x_0_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_9 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_9 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_9 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_2_9) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_2 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_9 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory322 (t x_2_9 : ℝ) : ((¬ (t ≤ x_2_9)) ↔ (¬ ((t + ((-1) * x_2_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_9) ↔ (((1) * t + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * t + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory323 (t x_1_7 : ℝ) : ((¬ (t ≤ x_1_7)) ↔ (¬ ((t + ((-1) * x_1_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_7) ↔ (((1) * t + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * t + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory324 (t x_1_7 x_1_9 x_7_9 : ℝ) : ((((x_1_7 ≤ x_1_9) ∧ (x_1_9 ≤ x_7_9) ∧ ((x_7_9 - x_1_7) ≥ 1) ∧ ((x_1_9 - x_1_7) ≤ (t - 1)) ∧ ((x_7_9 - x_1_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_7) ∧ ((x_1_7 - x_7_9) ≥ 1) ∧ ((x_1_7 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_1_7 ≤ x_1_9) ∧ (x_1_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_1_9) ↔ (((1) * x_1_7 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_9 ≤ x_7_9) ↔ (((1) * x_1_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_1_7) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_9 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory325 (t x_2_4 x_2_8 x_4_8 : ℝ) : ((((x_2_4 ≤ x_2_8) ∧ (x_2_8 ≤ x_4_8) ∧ ((x_4_8 - x_2_4) ≥ 1) ∧ ((x_2_8 - x_2_4) ≤ (t - 1)) ∧ ((x_4_8 - x_2_8) ≤ (t - 1))) ∨ ((x_4_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_4) ∧ ((x_2_4 - x_4_8) ≥ 1) ∧ ((x_2_4 - x_2_8) ≤ (t - 1)) ∧ ((x_2_8 - x_4_8) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_8) ∧ (x_2_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_4_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_4 ≤ x_2_8) ↔ (((1) * x_2_4 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_8 ≤ x_4_8) ↔ (((1) * x_2_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_8 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_8 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_8 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_4_8) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_4 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_8 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory326 (x_1_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory327 (x_0_5 x_1_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory328 (t x_0_6 x_0_9 x_6_9 : ℝ) : ((((x_0_6 ≤ x_0_9) ∧ (x_0_9 ≤ x_6_9) ∧ ((x_6_9 - x_0_6) ≥ 1) ∧ ((x_0_9 - x_0_6) ≤ (t - 1)) ∧ ((x_6_9 - x_0_9) ≤ (t - 1))) ∨ ((x_6_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_6) ∧ ((x_0_6 - x_6_9) ≥ 1) ∧ ((x_0_6 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_6_9) ≤ (t - 1)))) ↔ (((x_0_6 ≤ x_0_9) ∧ (x_0_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_6_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_6 ≤ x_0_9) ↔ (((1) * x_0_6 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_9 ≤ x_6_9) ↔ (((1) * x_0_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_0_6) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_9 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_9 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_6 - x_6_9) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_6 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_9 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory329 (x_2_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory330 (x_0_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory331 (x_1_3 x_3_5 x_3_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory332 (x_0_3 x_1_3 x_3_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory333 (x_1_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≤ 0)) ∨ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory334 (x_1_7 x_2_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory335 (t x_2_10 x_2_9 x_9_10 : ℝ) : ((((x_2_9 ≤ x_2_10) ∧ (x_2_10 ≤ x_9_10) ∧ ((x_9_10 - x_2_9) ≥ 1) ∧ ((x_2_10 - x_2_9) ≤ (t - 1)) ∧ ((x_9_10 - x_2_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_9) ∧ ((x_2_9 - x_9_10) ≥ 1) ∧ ((x_2_9 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_2_9 ≤ x_2_10) ∧ (x_2_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_9 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_10 ≤ x_9_10) ↔ (((1) * x_2_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_9_10 - x_2_9) ≥ 1) ↔ (((1) * x_2_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_10 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_9_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_9_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_2_9) ↔ (((1) * x_2_10 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_2_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_9 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_9_10 + ((-1) * x_2_9)) ≥ 1) ↔ (((1) * x_2_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_10 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_9_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_2_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_9 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory336 (t x_5_10 x_5_9 x_9_10 : ℝ) : ((((x_5_9 ≤ x_5_10) ∧ (x_5_10 ≤ x_9_10) ∧ ((x_9_10 - x_5_9) ≥ 1) ∧ ((x_5_10 - x_5_9) ≤ (t - 1)) ∧ ((x_9_10 - x_5_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_9) ∧ ((x_5_9 - x_9_10) ≥ 1) ∧ ((x_5_9 - x_5_10) ≤ (t - 1)) ∧ ((x_5_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_5_9 ≤ x_5_10) ∧ (x_5_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_5_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_9 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_10 ≤ x_9_10) ↔ (((1) * x_5_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_9_10 - x_5_9) ≥ 1) ↔ (((1) * x_5_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_10 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_9_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_9_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_10 ≤ x_5_9) ↔ (((1) * x_5_10 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_5_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_9 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_5_9)) ≥ 1) ↔ (((1) * x_5_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_10 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_9_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_9 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory337 (x_2_4 x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory338 (x_0_2 x_1_2 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory339 (x_1_2 x_2_7 x_2_8 : ℝ) : (¬ ((x_2_7 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory340 (x_1_2 x_1_7 x_2_4 x_2_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory341 (x_1_2 x_2_6 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory342 (x_0_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory343 (x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory344 (x_2_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory345 (x_0_5 x_0_8 x_2_5 x_5_8 : ℝ) : (¬ ((x_0_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory346 (x_1_2 x_1_4 x_2_5 x_4_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory347 (x_3_7 x_5_7 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory349 (t x_1_10 x_1_9 x_9_10 : ℝ) : ((((x_1_9 ≤ x_1_10) ∧ (x_1_10 ≤ x_9_10) ∧ ((x_9_10 - x_1_9) ≥ 1) ∧ ((x_1_10 - x_1_9) ≤ (t - 1)) ∧ ((x_9_10 - x_1_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_9) ∧ ((x_1_9 - x_9_10) ≥ 1) ∧ ((x_1_9 - x_1_10) ≤ (t - 1)) ∧ ((x_1_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_1_9 ≤ x_1_10) ∧ (x_1_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_1_9)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_9) ∧ ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_9 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_10 ≤ x_9_10) ↔ (((1) * x_1_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_9_10 - x_1_9) ≥ 1) ↔ (((1) * x_1_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_10 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_9_10 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_9_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_10 ≤ x_1_9) ↔ (((1) * x_1_10 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_1_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_9 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_9_10 + ((-1) * x_1_9)) ≥ 1) ↔ (((1) * x_1_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_10 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_9_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_1_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_9 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory350 (t x_2_10 x_2_5 x_5_10 : ℝ) : ((((x_2_5 ≤ x_2_10) ∧ (x_2_10 ≤ x_5_10) ∧ ((x_5_10 - x_2_5) ≥ 1) ∧ ((x_2_10 - x_2_5) ≤ (t - 1)) ∧ ((x_5_10 - x_2_10) ≤ (t - 1))) ∨ ((x_5_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_5) ∧ ((x_2_5 - x_5_10) ≥ 1) ∧ ((x_2_5 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_5_10) ≤ (t - 1)))) ↔ (((x_2_5 ≤ x_2_10) ∧ (x_2_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_5_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_5 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_10 ≤ x_5_10) ↔ (((1) * x_2_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_10 - x_2_5) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_10 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_10 ≤ x_2_5) ↔ (((1) * x_2_10 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_5 - x_5_10) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_5 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_10 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory351 (t x_4_10 x_4_5 x_5_10 : ℝ) : ((((x_4_5 ≤ x_4_10) ∧ (x_4_10 ≤ x_5_10) ∧ ((x_5_10 - x_4_5) ≥ 1) ∧ ((x_4_10 - x_4_5) ≤ (t - 1)) ∧ ((x_5_10 - x_4_10) ≤ (t - 1))) ∨ ((x_5_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_5) ∧ ((x_4_5 - x_5_10) ≥ 1) ∧ ((x_4_5 - x_4_10) ≤ (t - 1)) ∧ ((x_4_10 - x_5_10) ≤ (t - 1)))) ↔ (((x_4_5 ≤ x_4_10) ∧ (x_4_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_5_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_5 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_10 ≤ x_5_10) ↔ (((1) * x_4_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_10 - x_4_5) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_10 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_4_5) ↔ (((1) * x_4_10 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 - x_5_10) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_10 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory352 (t x_5_10 x_5_6 x_6_10 : ℝ) : ((((x_5_6 ≤ x_5_10) ∧ (x_5_10 ≤ x_6_10) ∧ ((x_6_10 - x_5_6) ≥ 1) ∧ ((x_5_10 - x_5_6) ≤ (t - 1)) ∧ ((x_6_10 - x_5_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_6) ∧ ((x_5_6 - x_6_10) ≥ 1) ∧ ((x_5_6 - x_5_10) ≤ (t - 1)) ∧ ((x_5_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_5_6 ≤ x_5_10) ∧ (x_5_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_5_6 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_10 ≤ x_6_10) ↔ (((1) * x_5_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_10 - x_5_6) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_10 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_10 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_5_6) ↔ (((1) * x_5_10 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_6 - x_5_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_6 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory354 (x_3_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory356 (x_3_6 x_5_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory357 (x_1_4 x_4_6 x_4_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_9)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory358 (x_0_5 x_0_8 x_5_7 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory359 (t x_2_3 x_2_9 x_3_9 : ℝ) : ((((x_2_3 ≤ x_2_9) ∧ (x_2_9 ≤ x_3_9) ∧ ((x_3_9 - x_2_3) ≥ 1) ∧ ((x_2_9 - x_2_3) ≤ (t - 1)) ∧ ((x_3_9 - x_2_9) ≤ (t - 1))) ∨ ((x_3_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_3) ∧ ((x_2_3 - x_3_9) ≥ 1) ∧ ((x_2_3 - x_2_9) ≤ (t - 1)) ∧ ((x_2_9 - x_3_9) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_9) ∧ (x_2_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_3_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_3 ≤ x_2_9) ↔ (((1) * x_2_3 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_9 ≤ x_3_9) ↔ (((1) * x_2_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_9 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_9 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_9 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_9 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_3_9) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 - x_2_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_9 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory360 (x_0_5 x_2_5 x_5_6 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory361 (x_1_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory362 (x_0_4 x_2_4 : ℝ) : ((x_0_4 + ((-1) * x_2_4)) ≤ 0) ∨ ((x_0_4 + ((-1) * x_2_4)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory363 (x_0_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory364 (x_0_4 x_2_4 x_4_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory365 (t x_0_10 x_0_9 x_9_10 : ℝ) : ((((x_0_9 ≤ x_0_10) ∧ (x_0_10 ≤ x_9_10) ∧ ((x_9_10 - x_0_9) ≥ 1) ∧ ((x_0_10 - x_0_9) ≤ (t - 1)) ∧ ((x_9_10 - x_0_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_9) ∧ ((x_0_9 - x_9_10) ≥ 1) ∧ ((x_0_9 - x_0_10) ≤ (t - 1)) ∧ ((x_0_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_0_9 ≤ x_0_10) ∧ (x_0_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_0_9)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_9) ∧ ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_9 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_10 ≤ x_9_10) ↔ (((1) * x_0_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_9_10 - x_0_9) ≥ 1) ↔ (((1) * x_0_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_10 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_9_10 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_9_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_10 ≤ x_0_9) ↔ (((1) * x_0_10 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_0_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_9 - x_0_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_9_10 + ((-1) * x_0_9)) ≥ 1) ↔ (((1) * x_0_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_10 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_9_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_0_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_9 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory366 (t x_0_10 x_0_9 x_9_10 : ℝ) : ((((x_0_9 + ((-1) * x_0_10)) ≤ 0) ∧ ((x_0_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_0_9 + ((-1) * x_0_10)) ≥ 1) ∧ ((t + x_0_10 + ((-1) * x_9_10)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_0_10)) ≤ 0)) ∨ (¬ ((x_0_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((t + x_0_9 + ((-1) * x_0_10)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1)))))) := by
  classical
  have e0 : ((x_0_9 + ((-1) * x_0_10)) ≤ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_0_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_0_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_9 + ((-1) * x_0_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory367 (t x_0_10 x_0_9 x_9_10 : ℝ) : ((((x_0_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_0_9 + ((-1) * x_0_10)) ≥ 0) ∧ ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_0_10) ≥ 1) ∧ ((t + ((-1) * x_0_10) + x_9_10) ≥ 1)) ↔ (¬ ((¬ ((x_0_9 + ((-1) * x_0_10)) ≥ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_9) + x_0_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_10) + x_9_10) ≥ 1)) ∨ (¬ ((x_0_10 + ((-1) * x_9_10)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_0_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_9 + ((-1) * x_0_10)) ≥ 0) ↔ (((1) * x_0_10 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_9) + x_0_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory368 (t x_0_9 : ℝ) : ((¬ (t ≤ x_0_9)) ↔ (¬ ((t + ((-1) * x_0_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_9) ↔ (((1) * t + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * t + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory369 (t x_6_10 x_6_7 x_7_10 : ℝ) : ((((x_6_7 ≤ x_6_10) ∧ (x_6_10 ≤ x_7_10) ∧ ((x_7_10 - x_6_7) ≥ 1) ∧ ((x_6_10 - x_6_7) ≤ (t - 1)) ∧ ((x_7_10 - x_6_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_7) ∧ ((x_6_7 - x_7_10) ≥ 1) ∧ ((x_6_7 - x_6_10) ≤ (t - 1)) ∧ ((x_6_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_6_7 ≤ x_6_10) ∧ (x_6_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_6_7 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_10 ≤ x_7_10) ↔ (((1) * x_6_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_10 - x_6_7) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_6_7) ↔ (((1) * x_6_10 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_6_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_7 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_7 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory370 (t x_1_10 x_1_4 x_4_10 : ℝ) : ((((x_1_4 ≤ x_1_10) ∧ (x_1_10 ≤ x_4_10) ∧ ((x_4_10 - x_1_4) ≥ 1) ∧ ((x_1_10 - x_1_4) ≤ (t - 1)) ∧ ((x_4_10 - x_1_10) ≤ (t - 1))) ∨ ((x_4_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_4) ∧ ((x_1_4 - x_4_10) ≥ 1) ∧ ((x_1_4 - x_1_10) ≤ (t - 1)) ∧ ((x_1_10 - x_4_10) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_10) ∧ (x_1_10 ≤ x_4_10) ∧ ((x_4_10 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_4_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_4 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_10 ≤ x_4_10) ↔ (((1) * x_1_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_10 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_10 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_10 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_10 ≤ x_1_4) ↔ (((1) * x_1_10 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_4_10) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_4 - x_1_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_10 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory371 (t x_1_10 x_1_4 x_4_10 : ℝ) : ((((x_1_4 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((x_1_10 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory372 (t x_1_10 x_1_4 x_4_10 : ℝ) : ((((x_1_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)) ↔ (¬ ((¬ ((x_1_10 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1))))) := by
  classical
  have e0 : ((x_1_10 + ((-1) * x_4_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_10) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory373 (x_1_7 x_3_7 x_7_9 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory374 (t x_1_6 : ℝ) : ((¬ (t ≤ x_1_6)) ↔ (¬ ((t + ((-1) * x_1_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_6) ↔ (((1) * t + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * t + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory376 (x_0_7 x_1_7 x_7_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory377 (x_0_6 x_2_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory378 (t x_0_1 x_0_9 x_1_9 : ℝ) : ((((x_0_1 ≤ x_0_9) ∧ (x_0_9 ≤ x_1_9) ∧ ((x_1_9 - x_0_1) ≥ 1) ∧ ((x_0_9 - x_0_1) ≤ (t - 1)) ∧ ((x_1_9 - x_0_9) ≤ (t - 1))) ∨ ((x_1_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_1) ∧ ((x_0_1 - x_1_9) ≥ 1) ∧ ((x_0_1 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_1_9) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_9) ∧ (x_0_9 ≤ x_1_9) ∧ ((x_1_9 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_1_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_9)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_1_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_1 ≤ x_0_9) ↔ (((1) * x_0_1 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_9 ≤ x_1_9) ↔ (((1) * x_0_9 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_9 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_9 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_9 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_1_9) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_1 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_9 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_9 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory379 (x_0_1 x_1_3 x_1_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory380 (t x_1_3 x_1_9 x_3_9 : ℝ) : ((((x_1_3 ≤ x_1_9) ∧ (x_1_9 ≤ x_3_9) ∧ ((x_3_9 - x_1_3) ≥ 1) ∧ ((x_1_9 - x_1_3) ≤ (t - 1)) ∧ ((x_3_9 - x_1_9) ≤ (t - 1))) ∨ ((x_3_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_3) ∧ ((x_1_3 - x_3_9) ≥ 1) ∧ ((x_1_3 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_3_9) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_9) ∧ (x_1_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_3_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_3 ≤ x_1_9) ↔ (((1) * x_1_3 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_9 ≤ x_3_9) ↔ (((1) * x_1_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_9 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_9 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_3_9) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_3 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory381 (t x_1_3 x_1_9 x_3_9 : ℝ) : ((((x_1_3 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_3_9)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_3 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((t + x_1_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)))))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_9 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_3 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_9 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory382 (t x_1_3 x_1_9 x_3_9 : ℝ) : ((((x_1_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_3_9) ≥ 1)) ↔ (¬ ((¬ ((x_1_9 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_9) + x_3_9) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_9)) ≥ 1))))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_9 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_1_3) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_9) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory383 (x_0_8 x_1_8 x_8_9 : ℝ) : (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory384 (x_0_1 x_1_3 x_1_8 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory385 (t x_4_10 x_4_7 x_7_10 : ℝ) : ((((x_4_7 ≤ x_4_10) ∧ (x_4_10 ≤ x_7_10) ∧ ((x_7_10 - x_4_7) ≥ 1) ∧ ((x_4_10 - x_4_7) ≤ (t - 1)) ∧ ((x_7_10 - x_4_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_7) ∧ ((x_4_7 - x_7_10) ≥ 1) ∧ ((x_4_7 - x_4_10) ≤ (t - 1)) ∧ ((x_4_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_4_7 ≤ x_4_10) ∧ (x_4_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_4_7 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_10 ≤ x_7_10) ↔ (((1) * x_4_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_10 - x_4_7) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_10 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_4_7) ↔ (((1) * x_4_10 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_7 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_7 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory386 (t x_3_9 : ℝ) : ((¬ (t ≤ x_3_9)) ↔ (¬ ((t + ((-1) * x_3_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_9) ↔ (((1) * t + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * t + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory388 (x_1_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory390 (x_0_2 x_1_2 x_2_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory391 (x_2_4 x_4_7 x_4_8 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≥ 0)) ∨ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory393 (x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory394 (x_0_3 x_2_3 x_3_8 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory395 (x_2_3 x_3_4 x_3_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_8)) ≤ 0)) ∨ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory396 (x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((x_4_5 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory397 (x_3_5 x_4_5 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory398 (t x_4_10 x_4_6 x_6_10 : ℝ) : ((((x_4_6 ≤ x_4_10) ∧ (x_4_10 ≤ x_6_10) ∧ ((x_6_10 - x_4_6) ≥ 1) ∧ ((x_4_10 - x_4_6) ≤ (t - 1)) ∧ ((x_6_10 - x_4_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_6) ∧ ((x_4_6 - x_6_10) ≥ 1) ∧ ((x_4_6 - x_4_10) ≤ (t - 1)) ∧ ((x_4_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_4_6 ≤ x_4_10) ∧ (x_4_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_6 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_10 ≤ x_6_10) ↔ (((1) * x_4_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_4_6) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_10 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_4_6) ↔ (((1) * x_4_10 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_10 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_6 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory401 (t x_3_10 x_3_4 x_4_10 : ℝ) : ((((x_3_4 ≤ x_3_10) ∧ (x_3_10 ≤ x_4_10) ∧ ((x_4_10 - x_3_4) ≥ 1) ∧ ((x_3_10 - x_3_4) ≤ (t - 1)) ∧ ((x_4_10 - x_3_10) ≤ (t - 1))) ∨ ((x_4_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_4) ∧ ((x_3_4 - x_4_10) ≥ 1) ∧ ((x_3_4 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_4_10) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_10) ∧ (x_3_10 ≤ x_4_10) ∧ ((x_4_10 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_4_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_4_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_4 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_10 ≤ x_4_10) ↔ (((1) * x_3_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_10 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_10 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_3_4) ↔ (((1) * x_3_10 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_4 - x_4_10) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_10 - x_4_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_10 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory402 (x_0_2 x_0_4 x_0_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≤ 0)) ∨ ((x_0_2 + ((-1) * x_0_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory403 (x_1_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_8 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_1_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory404 (x_0_2 x_1_2 x_2_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory405 (t x_2_10 x_2_6 x_6_10 : ℝ) : ((((x_2_6 ≤ x_2_10) ∧ (x_2_10 ≤ x_6_10) ∧ ((x_6_10 - x_2_6) ≥ 1) ∧ ((x_2_10 - x_2_6) ≤ (t - 1)) ∧ ((x_6_10 - x_2_10) ≤ (t - 1))) ∨ ((x_6_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_6) ∧ ((x_2_6 - x_6_10) ≥ 1) ∧ ((x_2_6 - x_2_10) ≤ (t - 1)) ∧ ((x_2_10 - x_6_10) ≤ (t - 1)))) ↔ (((x_2_6 ≤ x_2_10) ∧ (x_2_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_6_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_6 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_10 ≤ x_6_10) ↔ (((1) * x_2_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_10 - x_2_6) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_10 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_10 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_10 ≤ x_2_6) ↔ (((1) * x_2_10 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_6 - x_6_10) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 - x_2_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 - x_6_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_10 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory406 (x_1_6 x_2_6 x_6_9 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory407 (x_0_3 x_3_7 x_3_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory408 (x_0_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ ((x_0_4 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory409 (x_1_4 x_1_6 x_4_7 x_6_7 : ℝ) : (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory410 (x_0_4 x_3_4 x_4_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory411 (x_0_4 x_3_4 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory412 (x_1_6 x_3_6 x_6_8 : ℝ) : (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory413 (x_1_6 x_4_6 : ℝ) : ((x_1_6 + ((-1) * x_4_6)) ≤ 0) ∨ ((x_1_6 + ((-1) * x_4_6)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory414 (t x_3_10 x_3_7 x_7_10 : ℝ) : ((((x_3_7 ≤ x_3_10) ∧ (x_3_10 ≤ x_7_10) ∧ ((x_7_10 - x_3_7) ≥ 1) ∧ ((x_3_10 - x_3_7) ≤ (t - 1)) ∧ ((x_7_10 - x_3_10) ≤ (t - 1))) ∨ ((x_7_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_7) ∧ ((x_3_7 - x_7_10) ≥ 1) ∧ ((x_3_7 - x_3_10) ≤ (t - 1)) ∧ ((x_3_10 - x_7_10) ≤ (t - 1)))) ↔ (((x_3_7 ≤ x_3_10) ∧ (x_3_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_7_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_7 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_10 ≤ x_7_10) ↔ (((1) * x_3_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_10 - x_3_7) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_10 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_10 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_10 ≤ x_3_7) ↔ (((1) * x_3_10 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_7 - x_7_10) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_7 - x_3_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_10 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_7 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory415 (t x_7_10 x_7_8 x_8_10 : ℝ) : ((((x_7_8 ≤ x_7_10) ∧ (x_7_10 ≤ x_8_10) ∧ ((x_8_10 - x_7_8) ≥ 1) ∧ ((x_7_10 - x_7_8) ≤ (t - 1)) ∧ ((x_8_10 - x_7_10) ≤ (t - 1))) ∨ ((x_8_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_8) ∧ ((x_7_8 - x_8_10) ≥ 1) ∧ ((x_7_8 - x_7_10) ≤ (t - 1)) ∧ ((x_7_10 - x_8_10) ≤ (t - 1)))) ↔ (((x_7_8 ≤ x_7_10) ∧ (x_7_10 ≤ x_8_10) ∧ ((x_8_10 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_7_10 + ((-1) * x_7_8)) ≤ ((-1) + t)) ∧ ((x_8_10 + ((-1) * x_7_10)) ≤ ((-1) + t))) ∨ ((x_8_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_8_10)) ≥ 1) ∧ ((x_7_8 + ((-1) * x_7_10)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_8_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_7_8 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_7_8 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_7_10 ≤ x_8_10) ↔ (((1) * x_7_10 + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_10 - x_7_8) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_10 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_8_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_7_8) ↔ (((1) * x_7_10 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_7_8 - x_8_10) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_8 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 - x_8_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_10 + ((-1) * x_7_8)) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_8 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_10 + ((-1) * x_8_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_8_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory416 (t x_7_10 : ℝ) : ((¬ (t ≤ x_7_10)) ↔ (¬ ((t + ((-1) * x_7_10)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_7_10) ↔ (((1) * t + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * t + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory417 (x_0_4 x_1_4 x_4_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory418 (x_1_6 x_3_6 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_3_6)) ≥ 0)) ∨ ((x_1_6 + ((-1) * x_6_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory419 (x_1_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

end ElevenTheory
