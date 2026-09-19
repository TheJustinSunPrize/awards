import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory1257 (t x_1_6 x_1_7 x_6_7 : ℝ) : ((((x_1_6 ≤ x_1_7) ∧ (x_1_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_6_7)) ≤ ((-1) + t)))) ↔ ((((x_1_6 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_6_7) ≥ 1)))) := by
  classical
  have e0 : ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_6 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_6) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_6 ≤ x_1_7) ↔ (((1) * x_1_6 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_6_7) ↔ (((1) * x_1_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_6 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1258 (x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1259 (t x_1_6 x_1_9 x_6_9 : ℝ) : ((((x_1_6 ≤ x_1_9) ∧ (x_1_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_1_6 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_6 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_6) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_6 ≤ x_1_9) ↔ (((1) * x_1_6 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_6_9) ↔ (((1) * x_1_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_6 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1260 (t x_1_6 x_4_8 x_6_8 x_6_9 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_8) + x_6_8) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1261 (t x_2_4 x_2_9 x_4_9 : ℝ) : ((((x_2_4 ≤ x_2_9) ∧ (x_2_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_4_9)) ≤ ((-1) + t)))) ↔ ((((x_2_4 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_4_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_9)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_9 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_4 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_9 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_4 ≤ x_2_9) ↔ (((1) * x_2_4 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_4_9) ↔ (((1) * x_2_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_9 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_4 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_4) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1262 (t x_2_3 x_2_4 x_3_4 x_3_6 x_4_9 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1263 (t x_3_4 x_3_9 x_4_9 : ℝ) : ((((x_3_4 ≤ x_3_9) ∧ (x_3_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_4_9)) ≤ ((-1) + t)))) ↔ ((((x_3_4 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_4_9) ≥ 1)))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_4_9)) ≤ (-1)) ↔ (((1) * x_3_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_9 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_4 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_3_4 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_3_9 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_3_9) ↔ (((1) * x_3_4 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_4_9) ↔ (((1) * x_3_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_9 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_9 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_4 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_3_4) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_3_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1264 (t x_0_4 x_0_9 x_4_9 : ℝ) : ((((x_0_4 ≤ x_0_9) ∧ (x_0_9 ≤ x_4_9) ∧ ((x_4_9 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_4_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_4_9)) ≤ ((-1) + t)))) ↔ ((((x_0_4 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_4_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_4 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_9 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_4 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_9 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_4 ≤ x_0_9) ↔ (((1) * x_0_4 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_4_9) ↔ (((1) * x_0_9 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_9 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_4 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_4 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_4) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1265 (t x_0_4 x_4_8 x_4_9 x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_8) + x_7_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_4_9 + ((-1) * x_8_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1266 (t x_1_2 x_2_3 x_2_4 x_3_4 x_3_5 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1267 (t x_0_3 x_1_2 x_1_3 x_2_3 x_2_4 x_3_5 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1268 (x_0_1 x_1_3 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1269 (t x_1_2 x_2_3 x_2_6 x_3_4 x_3_6 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1270 (t x_1_2 x_2_3 x_2_4 x_3_4 x_3_6 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1271 (t x_0_1 x_0_4 x_1_4 : ℝ) : ((((x_0_1 ≤ x_0_4) ∧ (x_0_4 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_1_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_1_4)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_4)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_1_4)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1) ∧ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (((x_0_4 + ((-1) * x_1_4)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_4)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_1_4) ≥ 1)))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_1_4)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_1_4)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_1 + ((-1) * x_0_4)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_1) + x_0_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((t + ((-1) * x_0_4) + x_1_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_1 ≤ x_0_4) ↔ (((1) * x_0_1 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_4 ≤ x_1_4) ↔ (((1) * x_0_4 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_1_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : (x_0_4 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_4) < 0)) := by
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
  have e16 : ((x_0_1 + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_0_1 + ((-1) * x_1_4)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1272 (t x_0_4 x_0_7 x_4_7 : ℝ) : ((((x_0_4 ≤ x_0_7) ∧ (x_0_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_4_7)) ≤ ((-1) + t)))) ↔ ((((x_0_4 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_7) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_4) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_4 ≤ x_0_7) ↔ (((1) * x_0_4 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_4_7) ↔ (((1) * x_0_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_7 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_4 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_4 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1273 (t x_0_1 x_0_7 x_1_7 : ℝ) : ((((x_0_1 ≤ x_0_7) ∧ (x_0_7 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_1_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_1_7)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_1_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_1_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_7 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_1 + ((-1) * x_1_7)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_1 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_7 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_7) ↔ (((1) * x_0_1 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_1_7) ↔ (((1) * x_0_7 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_7 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_1) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_7) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1274 (t x_0_1 x_1_3 x_1_7 x_3_4 x_3_7 : ℝ) : (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1275 (t x_0_1 x_0_3 x_1_3 x_3_7 : ℝ) : (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory1276 (t x_0_1 x_1_3 x_1_4 x_3_4 x_3_5 : ℝ) : (¬ ((t + x_3_4 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1277 (t x_1_2 x_1_4 x_2_4 : ℝ) : ((((x_1_2 ≤ x_1_4) ∧ (x_1_4 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_1_4)) ≤ ((-1) + t))) ∨ ((x_2_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_2_4)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_4)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_2_4)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1) ∧ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (((x_1_4 + ((-1) * x_2_4)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_4)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_2_4)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_1_2) + x_1_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_2_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_2 + ((-1) * x_1_4)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_4 + ((-1) * x_2_4)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_2 ≤ x_1_4) ↔ (((1) * x_1_2 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_4 ≤ x_2_4) ↔ (((1) * x_1_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_4 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_1_4 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_4 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_4 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_2 + ((-1) * x_1_4)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_2_4)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1278 (t x_1_3 x_3_4 x_3_5 x_4_5 x_4_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1279 (x_1_3 x_3_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1281 (t x_2_4 x_2_6 x_4_6 : ℝ) : ((((x_2_4 ≤ x_2_6) ∧ (x_2_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_4_6)) ≤ ((-1) + t)))) ↔ ((((x_2_4 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (((x_2_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_6) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_4_6) ≥ 1)))) := by
  classical
  have e0 : ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_4 ≤ x_2_6) ↔ (((1) * x_2_4 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_6 ≤ x_4_6) ↔ (((1) * x_2_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_4_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : (x_2_6 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_6 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_6 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_4 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_4 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_4 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_4) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1282 (t x_0_2 x_0_3 x_2_3 x_2_4 x_3_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1283 (t x_0_2 x_0_3 x_2_3 x_2_6 x_3_4 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1284 (t x_0_6 x_0_7 x_2_6 x_6_7 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_0_6) + x_2_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1285 (t x_2_7 x_2_9 x_7_9 : ℝ) : ((((x_2_7 ≤ x_2_9) ∧ (x_2_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_2_7 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_2_7 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_2_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_7 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_7 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_7 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_7 ≤ x_2_9) ↔ (((1) * x_2_7 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_7_9) ↔ (((1) * x_2_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_7 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_7 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_7) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1286 (t x_0_3 x_1_4 x_3_4 x_3_8 x_4_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1287 (t x_0_1 x_0_8 x_1_8 : ℝ) : ((((x_0_1 ≤ x_0_8) ∧ (x_0_8 ≤ x_1_8) ∧ ((x_1_8 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_1_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_1_8)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_1_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_1_8) ≥ 1)))) := by
  classical
  have e0 : ((x_0_8 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_8 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_1 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_1 + ((-1) * x_1_8)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_8) ↔ (((1) * x_0_1 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_1_8) ↔ (((1) * x_0_8 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_8 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_1) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_8) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1288 (t x_6_10 x_6_9 x_9_10 : ℝ) : ((((x_6_9 ≤ x_6_10) ∧ (x_6_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_6_9 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_6_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_6_9 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + x_6_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_6_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_6_9 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_6_9) + x_6_10) ≥ 1) ∧ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_6_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_6_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_6_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_6_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_9 + ((-1) * x_6_10)) ≤ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_6_9 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_6_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_9 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_9_10) ↔ (((1) * x_6_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_10 ≤ x_6_9) ↔ (((1) * x_6_10 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_6_9)) ≥ 1) ↔ (((1) * x_6_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_6_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_9 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_9 + ((-1) * x_6_10)) ≥ 0) ↔ (((1) * x_6_10 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_6_9) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_6_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1289 (t x_0_2 x_0_7 x_2_7 : ℝ) : ((((x_0_2 ≤ x_0_7) ∧ (x_0_7 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_2_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_2_7)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_2_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_2_7) ≥ 1)))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_7)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_2 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_7 + ((-1) * x_2_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_2 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_7 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_2 ≤ x_0_7) ↔ (((1) * x_0_2 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_7 ≤ x_2_7) ↔ (((1) * x_0_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_7 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_7 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_2) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_7) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1290 (t x_2_6 x_2_9 x_6_9 : ℝ) : ((((x_2_6 ≤ x_2_9) ∧ (x_2_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_2_6 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_2_6 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_6 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_6) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_6 ≤ x_2_9) ↔ (((1) * x_2_6 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_6_9) ↔ (((1) * x_2_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_2_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_6 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1291 (x_1_4 x_4_5 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1292 (t x_0_2 x_1_3 x_2_3 x_2_7 x_3_7 : ℝ) : (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1293 (t x_3_6 x_3_9 x_6_9 : ℝ) : ((((x_3_6 ≤ x_3_9) ∧ (x_3_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_3_6 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_3_6 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_6 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_6) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_6 ≤ x_3_9) ↔ (((1) * x_3_6 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_9 ≤ x_6_9) ↔ (((1) * x_3_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_9 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_6 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_3_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_6 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1296 (t x_0_1 x_1_4 x_1_5 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1297 (x_1_2 x_2_4 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1298 (t x_3_10 x_3_9 x_9_10 : ℝ) : ((((x_3_9 ≤ x_3_10) ∧ (x_3_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_3_10 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_3_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_3_10) ∧ (x_3_10 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_10)) ≤ ((-1) + t)) ∧ ((x_3_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_3_9 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_3_9 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_3_9 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_3_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_3_9 + ((-1) * x_3_10)) ≥ 0) ↔ (((1) * x_3_10 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_3_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_3_9) + x_3_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_3_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_9 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_10 ≤ x_9_10) ↔ (((1) * x_3_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_3_10) ↔ (¬ (((1) * x_3_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_3_10 ≤ x_3_9) ↔ (((1) * x_3_10 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_3_9)) ≥ 1) ↔ (((1) * x_3_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_10 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_9 + ((-1) * x_3_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_9 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_3_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_3_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_3_9 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_3_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1299 (t x_0_7 x_0_9 x_7_9 : ℝ) : ((((x_0_7 ≤ x_0_9) ∧ (x_0_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_0_7 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_0_7 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_7) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_7 ≤ x_0_9) ↔ (((1) * x_0_7 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_7_9) ↔ (((1) * x_0_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_0_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_7 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1300 (t x_0_7 x_2_6 x_4_7 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1301 (x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1302 (t x_1_7 x_1_8 x_7_8 : ℝ) : ((((x_1_7 ≤ x_1_8) ∧ (x_1_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_7_8)) ≤ ((-1) + t)))) ↔ ((((x_1_7 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_1_7 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_7_8) ≥ 1)))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) ↔ (((1) * x_1_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_8 + ((-1) * x_7_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_7 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((t + ((-1) * x_1_7) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((t + ((-1) * x_1_8) + x_7_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_7 ≤ x_1_8) ↔ (((1) * x_1_7 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_1_8 ≤ x_7_8) ↔ (((1) * x_1_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : (x_7_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : (x_1_8 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_8 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_1_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_7 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1303 (x_1_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1304 (x_0_1 x_1_2 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1305 (t x_0_6 x_0_7 x_4_6 x_6_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1306 (t x_0_4 x_1_2 x_2_4 x_2_7 x_4_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1307 (t x_1_4 x_2_3 x_3_4 x_3_6 x_4_6 : ℝ) : (¬ ((x_3_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_1_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1308 (t x_0_1 x_0_4 x_1_2 x_1_4 x_4_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1309 (t x_1_2 x_1_8 x_2_8 : ℝ) : ((((x_1_2 ≤ x_1_8) ∧ (x_1_8 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_2_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_2_8)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_2_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_2_8) ≥ 1)))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_2) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_1_8) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_1_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_2 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_2 ≤ x_1_8) ↔ (((1) * x_1_2 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_2_8) ↔ (((1) * x_1_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_8 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_8 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_2_8)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_8 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1310 (t x_0_1 x_1_3 x_1_4 x_3_4 x_3_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1311 (t x_0_1 x_0_3 x_1_2 x_1_3 x_1_4 x_3_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1312 (t x_0_5 x_2_5 x_2_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_2_5 + ((-1) * x_2_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1313 (t x_0_3 x_2_4 x_3_4 x_3_5 x_4_5 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1314 (x_0_2 x_2_3 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1315 (t x_0_7 x_1_3 x_1_7 x_2_3 x_3_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1316 (t x_0_6 x_0_7 x_1_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_6) + x_1_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1319 (t x_1_7 x_3_6 x_6_7 x_6_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1320 (t x_1_5 x_1_7 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + x_1_5 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1321 (t x_1_5 x_1_7 x_5_6 x_5_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1322 (t x_1_7 x_5_6 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1323 (t x_0_1 x_1_4 x_1_7 x_4_5 x_4_7 : ℝ) : (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1325 (t x_0_7 x_5_7 x_5_8 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_7) + x_5_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_8)) ≤ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1327 (t x_4_6 x_6_8 x_6_9 x_7_8 x_8_9 : ℝ) : (¬ ((x_6_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_6_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1328 (t x_1_4 x_2_4 x_2_5 x_4_5 x_5_9 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1329 (x_0_2 x_2_4 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1330 (x_0_3 x_3_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1332 (x_0_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1333 (t x_1_4 x_1_7 x_3_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1334 (t x_4_6 x_4_9 x_6_9 : ℝ) : ((((x_4_6 ≤ x_4_9) ∧ (x_4_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_4_6 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_4_6 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + x_4_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_4_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_4_9) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_4_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_4_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_6 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_6) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + ((-1) * x_4_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_4_9) ↔ (((1) * x_4_6 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_6_9) ↔ (((1) * x_4_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : (x_4_9 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_9 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_9 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_6 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_4_6 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_4_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_6 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1335 (t x_3_4 x_3_7 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_6) + x_4_7) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1337 (t x_0_8 x_1_7 x_2_3 x_3_7 x_3_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1338 (t x_0_3 x_1_7 x_3_7 x_3_8 x_7_8 : ℝ) : (¬ ((x_3_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1339 (x_0_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1340 (t x_0_3 x_1_4 x_3_4 x_3_6 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1341 (t x_0_4 x_3_4 x_4_6 x_4_8 x_6_7 x_6_8 : ℝ) : (¬ ((x_4_8 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_6_7) + x_6_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1342 (t x_0_6 x_4_6 x_4_7 x_6_7 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1343 (x_4_7 x_7_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1344 (t x_1_4 x_4_5 x_4_7 x_5_7 x_5_8 : ℝ) : (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((t + x_5_7 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1345 (t x_0_7 x_4_5 x_5_7 x_5_8 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1346 (t x_0_3 x_0_5 x_3_5 x_3_6 x_5_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1348 (t x_1_3 x_3_5 x_3_6 x_5_6 x_5_8 : ℝ) : (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1349 (t x_3_7 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_3_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1350 (t x_1_7 x_6_7 x_6_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_8)) ≥ 0)) ∨ (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1351 (t x_0_2 x_1_2 x_1_7 x_2_7 x_7_8 : ℝ) : (¬ ((x_1_2 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1353 (t x_0_2 x_0_4 x_1_2 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1354 (t x_0_4 x_1_2 x_2_4 x_2_5 x_4_5 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1355 (t x_0_3 x_1_2 x_1_3 x_2_3 x_2_4 x_3_5 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1356 (x_0_7 x_3_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_3_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1357 (t x_0_4 x_0_7 x_2_4 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1358 (t x_0_1 x_1_3 x_1_5 x_2_3 x_3_5 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1359 (t x_0_1 x_0_2 x_1_2 x_1_3 x_2_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1360 (t x_0_1 x_1_2 x_1_3 x_2_3 x_2_4 : ℝ) : (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1361 (t x_0_2 x_0_3 x_2_3 x_2_5 x_3_4 : ℝ) : (¬ ((t + ((-1) * x_2_3) + x_2_5) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1362 (x_1_2 x_2_5 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1363 (x_0_2 x_2_3 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory1365 (t x_0_2 x_1_2 x_1_4 x_2_4 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_0_2) + x_1_2) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1366 (t x_1_4 x_1_5 x_2_4 x_4_5 x_5_7 : ℝ) : (¬ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1367 (t x_1_2 x_2_5 x_2_6 x_5_6 x_5_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1368 (x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1370 (x_0_5 x_5_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1371 (x_2_5 x_5_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1372 (x_1_2 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1374 (t x_1_2 x_1_9 x_2_9 : ℝ) : ((((x_1_2 ≤ x_1_9) ∧ (x_1_9 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_2_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_2_9)) ≤ ((-1) + t)))) ↔ ((((x_1_2 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_9)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_2_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_2_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_9)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_9 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_1_2 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_9 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_2 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_2 ≤ x_1_9) ↔ (((1) * x_1_2 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_2_9) ↔ (((1) * x_1_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_9 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_2 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_2) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_9) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1375 (t x_2_8 x_2_9 x_8_9 : ℝ) : ((((x_2_8 ≤ x_2_9) ∧ (x_2_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_8_9)) ≤ ((-1) + t)))) ↔ ((((x_2_8 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_2_8 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_8_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_2_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_9 + ((-1) * x_8_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_8 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_8) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_9) + x_8_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_8 ≤ x_2_9) ↔ (((1) * x_2_8 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_8_9) ↔ (((1) * x_2_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_8_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_8_9 + ((-1) * x_2_8)) ≥ 1) ↔ (((1) * x_2_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_8 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_8 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_2_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_8 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1376 (t x_0_2 x_0_9 x_2_9 : ℝ) : ((((x_0_2 ≤ x_0_9) ∧ (x_0_9 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_2_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_2_9)) ≤ ((-1) + t)))) ↔ ((((x_0_2 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_9)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_2_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_2_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_9 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_2) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_9) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_2 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_2 ≤ x_0_9) ↔ (((1) * x_0_2 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_2_9) ↔ (((1) * x_0_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_9 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_2 + ((-1) * x_2_9)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_2 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_9 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1378 (t x_0_1 x_0_3 x_1_2 x_2_7 x_3_6 x_6_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory1379 (t x_1_7 x_1_9 x_7_9 : ℝ) : ((((x_1_7 ≤ x_1_9) ∧ (x_1_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_1_7)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_7) ∧ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_7_9)) ≤ ((-1) + t)))) ↔ ((((x_1_7 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_1_7 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_7_9) ≥ 1)))) := by
  classical
  have e0 : ((x_1_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_1_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_7) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_7 ≤ x_1_9) ↔ (((1) * x_1_7 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_7_9) ↔ (((1) * x_1_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 + ((-1) * x_1_7)) ≥ 1) ↔ (((1) * x_1_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_7 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_7 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_1_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_7 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1380 (t x_1_2 x_2_4 x_2_5 x_4_5 x_4_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1381 (t x_1_2 x_2_5 x_2_6 x_2_7 x_3_5 x_5_7 : ℝ) : (¬ ((x_2_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((t + x_2_5 + ((-1) * x_3_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1382 (t x_0_1 x_0_3 x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1383 (t x_0_1 x_1_5 x_1_6 x_4_5 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((t + ((-1) * x_1_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_1_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1384 (t x_3_5 x_4_7 x_5_7 x_5_8 x_7_8 : ℝ) : (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((t + x_4_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1385 (t x_0_7 x_4_7 x_4_8 x_7_8 x_8_9 : ℝ) : (¬ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_4_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1386 (t x_0_7 x_1_2 x_2_7 x_2_8 x_7_8 : ℝ) : (¬ ((x_2_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_7) + x_2_7) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1387 (t x_2_4 x_2_8 x_4_8 : ℝ) : ((((x_2_4 ≤ x_2_8) ∧ (x_2_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_4_8)) ≤ ((-1) + t)))) ↔ ((((x_2_4 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_4_8) ≥ 1)))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_8 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_2_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_4) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_8) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_4 ≤ x_2_8) ↔ (((1) * x_2_4 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_4_8) ↔ (((1) * x_2_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_8 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_8 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1388 (t x_0_7 x_2_4 x_4_7 x_4_8 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1389 (t x_0_3 x_0_7 x_1_7 x_3_5 x_3_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_7) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1390 (t x_0_4 x_1_5 x_2_4 x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1391 (t x_0_6 x_0_9 x_6_9 : ℝ) : ((((x_0_6 ≤ x_0_9) ∧ (x_0_9 ≤ x_6_9) ∧ ((x_6_9 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_6_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_6_9)) ≤ ((-1) + t)))) ↔ ((((x_0_6 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_6_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_9) + x_6_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_9 + ((-1) * x_6_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_6 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_6) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_6 ≤ x_0_9) ↔ (((1) * x_0_6 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_6_9) ↔ (((1) * x_0_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_6 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1392 (t x_0_6 x_0_7 x_1_7 x_6_7 x_6_9 x_7_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((t + x_6_7 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1393 (t x_0_4 x_1_2 x_2_4 x_2_6 x_4_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1394 (t x_0_6 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1396 (t x_0_8 x_2_7 x_3_7 x_3_8 x_7_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + x_2_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_3_8)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1397 (t x_0_7 x_0_8 x_2_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_7 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_7) + x_2_7) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1398 (t x_0_3 x_0_4 x_1_3 x_3_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1399 (t x_0_4 x_1_3 x_3_4 x_3_5 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_0_4) + x_3_4) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1401 (t x_1_3 x_1_5 x_3_5 x_3_8 x_5_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_5) + x_3_8) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_5)) ≤ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1402 (t x_0_3 x_2_3 x_2_4 x_3_4 x_4_5 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1403 (t x_1_3 x_3_5 x_3_6 x_5_6 x_5_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_9)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1404 (t x_1_7 x_2_6 x_2_7 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_2_6 + ((-1) * x_2_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1405 (t x_0_3 x_2_3 x_2_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_2_3) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1407 (t x_1_7 x_3_7 x_4_6 x_6_7 x_6_8 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_3_7 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1408 (x_7_8 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1409 (t x_2_7 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((t + x_2_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1410 (t x_2_7 x_3_7 x_4_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_3_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1411 (t x_2_10 x_2_9 x_9_10 : ℝ) : ((((x_2_9 ≤ x_2_10) ∧ (x_2_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_2_9)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_9) ∧ ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_2_9 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_2_9 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_2_9 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_2_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_2_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_9 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_2_9 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_2_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_9 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_9_10) ↔ (((1) * x_2_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_10 ≤ x_2_9) ↔ (((1) * x_2_10 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_2_9)) ≥ 1) ↔ (((1) * x_2_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_2_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_9 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_2_9) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_2_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1412 (t x_5_10 x_5_9 x_9_10 : ℝ) : ((((x_5_9 ≤ x_5_10) ∧ (x_5_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_5_9 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_5_9 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_5_9 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_5_9 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_5_9) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_5_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_9 + ((-1) * x_5_10)) ≥ 0) ↔ (((1) * x_5_10 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_5_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_5_9) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_5_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_5_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_5_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_5_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_9 + ((-1) * x_5_10)) ≤ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_5_9 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_5_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : (x_5_9 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : (x_5_10 ≤ x_9_10) ↔ (((1) * x_5_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : (x_9_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : (x_5_10 ≤ x_5_9) ↔ (((1) * x_5_10 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_9_10 + ((-1) * x_5_9)) ≥ 1) ↔ (((1) * x_5_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_9_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((x_5_9 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((x_5_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1413 (t x_4_6 x_6_8 x_6_9 x_7_8 x_8_9 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_6_8) + x_7_8) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1414 (t x_1_4 x_4_7 x_4_8 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_4_7) + x_5_7) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1416 (t x_0_4 x_2_4 x_2_5 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1417 (t x_0_5 x_2_7 x_5_7 x_5_8 x_7_8 : ℝ) : (¬ ((x_5_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((t + x_2_7 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1419 (x_1_4 x_4_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1420 (t x_0_4 x_0_7 x_2_3 x_2_7 x_3_4 x_3_6 x_7_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1421 (x_3_5 x_5_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1422 (t x_1_4 x_4_5 x_4_6 x_5_6 x_5_7 : ℝ) : (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1424 (t x_0_1 x_0_2 x_1_2 x_2_4 x_2_5 x_2_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_2_5)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_7) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1425 (t x_2_7 x_3_6 x_6_7 x_6_9 x_7_9 : ℝ) : (¬ ((x_6_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_2_7 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1426 (t x_4_7 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_6_9)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1427 (t x_1_10 x_1_9 x_9_10 : ℝ) : ((((x_1_9 ≤ x_1_10) ∧ (x_1_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_1_9)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_9) ∧ ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_1_9 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_1_9 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_1_9 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : ((x_1_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_1_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_9 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_9 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_9 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_10 ≤ x_9_10) ↔ (((1) * x_1_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_9_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_10 ≤ x_1_9) ↔ (((1) * x_1_10 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_9_10 + ((-1) * x_1_9)) ≥ 1) ↔ (((1) * x_1_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_1_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_9 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_1_9) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_1_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1428 (t x_2_10 x_2_5 x_5_10 : ℝ) : ((((x_2_5 ≤ x_2_10) ∧ (x_2_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_10 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_2_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_2_10) ∧ (x_2_10 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_10)) ≤ ((-1) + t)) ∧ ((x_2_10 + ((-1) * x_5_10)) ≤ ((-1) + t)))) ↔ ((((x_2_5 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_10)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_5_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_5_10) ≥ 1)))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_10 + ((-1) * x_5_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_5) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_10) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_10 ≤ x_5_10) ↔ (((1) * x_2_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_10 ≤ x_2_10) ↔ (¬ (((1) * x_2_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_10 ≤ x_2_5) ↔ (((1) * x_2_10 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_10 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_2_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_10 + ((-1) * x_5_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_5 + ((-1) * x_5_10)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_5 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_10 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1429 (t x_0_4 x_2_4 x_2_5 x_4_5 x_5_10 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1430 (t x_4_10 x_4_5 x_5_10 : ℝ) : ((((x_4_5 ≤ x_4_10) ∧ (x_4_10 ≤ x_5_10) ∧ ((x_5_10 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_10 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_4_10)) ≤ ((-1) + t))) ∨ ((x_5_10 ≤ x_4_10) ∧ (x_4_10 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_10)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_5_10)) ≤ ((-1) + t)))) ↔ ((((x_4_5 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_4_5 + ((-1) * x_5_10)) ≤ (-1)) ∧ ((t + x_4_5 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_5_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + ((-1) * x_4_5) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_5_10) ≥ 1)))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_4_10 + ((-1) * x_5_10)) ≥ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_5 + ((-1) * x_4_10)) ≥ 0) ↔ (((1) * x_4_10 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_4_5) + x_4_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_4_10) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_5 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_10 ≤ x_5_10) ↔ (((1) * x_4_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_10 ≤ x_4_10) ↔ (¬ (((1) * x_4_10 + (-1) * x_5_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_4_10 ≤ x_4_5) ↔ (((1) * x_4_10 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_10 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_10 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_10 + ((-1) * x_5_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_4_5 + ((-1) * x_5_10)) ≤ (-1)) ↔ (((1) * x_4_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_4_5 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_4_10 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1431 (t x_1_4 x_4_5 x_4_6 x_5_10 x_5_6 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_10)) ≤ (-1))) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1432 (t x_5_10 x_5_6 x_6_10 : ℝ) : ((((x_5_6 ≤ x_5_10) ∧ (x_5_10 ≤ x_6_10) ∧ ((x_6_10 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_10 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_5_10)) ≤ ((-1) + t))) ∨ ((x_6_10 ≤ x_5_10) ∧ (x_5_10 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_10)) ≤ ((-1) + t)) ∧ ((x_5_10 + ((-1) * x_6_10)) ≤ ((-1) + t)))) ↔ ((((x_5_6 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_5_6 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_5_6) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_6_10) ≥ 1)))) := by
  classical
  have e0 : ((t + x_5_6 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_5_10 + ((-1) * x_6_10)) ≤ 0) ↔ (((1) * x_5_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 + ((-1) * x_6_10)) ≤ (-1)) ↔ (((1) * x_5_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_6 + ((-1) * x_5_10)) ≤ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_5_10 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_10 ≤ x_6_10) ↔ (((1) * x_5_10 + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_10 ≤ x_5_10) ↔ (¬ (((1) * x_5_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_5_10 ≤ x_5_6) ↔ (((1) * x_5_10 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_10 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_10 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_10 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_5_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_5_6 + ((-1) * x_5_10)) ≥ 0) ↔ (((1) * x_5_10 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_5_6) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_5_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1433 (t x_1_4 x_4_5 x_4_7 x_5_7 x_5_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((t + x_5_7 + ((-1) * x_5_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1434 (t x_0_4 x_2_4 x_2_5 x_4_5 x_5_9 : ℝ) : (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1435 (t x_0_2 x_1_5 x_2_5 x_2_7 x_5_7 : ℝ) : (¬ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1436 (t x_0_3 x_3_5 x_3_7 x_4_5 x_5_7 : ℝ) : (¬ ((t + ((-1) * x_3_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1437 (t x_1_2 x_2_4 x_2_5 x_4_5 x_4_6 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1439 (t x_0_4 x_0_5 x_4_5 x_4_6 x_5_7 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1440 (t x_0_4 x_0_5 x_2_4 x_4_5 x_5_9 : ℝ) : (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1441 (x_2_4 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1442 (x_4_5 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1443 (t x_0_4 x_0_5 x_2_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1444 (t x_0_7 x_1_4 x_2_7 x_4_7 x_4_8 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_2_7) + x_4_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1445 (t x_2_5 x_4_5 x_4_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1446 (t x_0_7 x_1_5 x_1_7 x_2_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_1_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1448 (t x_2_3 x_2_9 x_3_9 : ℝ) : ((((x_2_3 ≤ x_2_9) ∧ (x_2_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_9 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_2_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_2_9) ∧ (x_2_9 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_9)) ≤ ((-1) + t)) ∧ ((x_2_9 + ((-1) * x_3_9)) ≤ ((-1) + t)))) ↔ ((((x_2_3 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_3_9) ≥ 1)))) := by
  classical
  have e0 : ((x_2_9 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_3 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_2_3) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_2_9) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_3 ≤ x_2_9) ↔ (((1) * x_2_3 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_9 ≤ x_3_9) ↔ (((1) * x_2_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_2_9) ↔ (¬ (((1) * x_2_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_2_9 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_9 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_2_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_9 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_2_3 + ((-1) * x_3_9)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_2_3 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_2_9 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1449 (x_3_5 x_5_8 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1450 (x_4_5 x_5_6 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1452 (t x_3_4 x_4_5 x_4_7 x_5_6 x_5_7 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_5_7)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1453 (t x_1_7 x_3_4 x_4_7 x_4_8 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1454 (t x_0_4 x_0_7 x_4_5 x_4_7 x_7_9 : ℝ) : (¬ ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1455 (x_2_4 x_4_6 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1457 (t x_0_6 x_4_6 x_4_7 x_6_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1458 (t x_0_7 x_1_3 x_3_7 x_3_8 x_7_8 : ℝ) : (¬ ((t + ((-1) * x_0_7) + x_3_7) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_7_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1459 (t x_0_7 x_1_4 x_1_7 x_4_5 x_4_6 x_4_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((t + ((-1) * x_4_5) + x_4_6) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory1460 (t x_0_3 x_1_4 x_3_4 x_3_5 x_4_5 : ℝ) : (¬ ((t + x_1_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_4_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1461 (x_3_4 x_4_5 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1462 (t x_0_10 x_0_9 x_9_10 : ℝ) : ((((x_0_9 ≤ x_0_10) ∧ (x_0_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_0_9)) ≥ 1) ∧ ((x_0_10 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_0_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_0_10) ∧ (x_0_10 ≤ x_0_9) ∧ ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_10)) ≤ ((-1) + t)) ∧ ((x_0_10 + ((-1) * x_9_10)) ≤ ((-1) + t)))) ↔ ((((x_0_9 + ((-1) * x_0_10)) ≤ 0) ∧ ((x_0_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_0_9 + ((-1) * x_0_10)) ≥ 1) ∧ ((t + x_0_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_0_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_0_9 + ((-1) * x_0_10)) ≥ 0) ∧ ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_0_10) ≥ 1) ∧ ((t + ((-1) * x_0_10) + x_9_10) ≥ 1)))) := by
  classical
  have e0 : (x_0_9 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_10 ≤ x_9_10) ↔ (((1) * x_0_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_9_10 ≤ x_0_10) ↔ (¬ (((1) * x_0_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : (x_0_10 ≤ x_0_9) ↔ (((1) * x_0_10 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_9_10 + ((-1) * x_0_9)) ≥ 1) ↔ (((1) * x_0_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_0_10 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_9_10 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_0_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_9 + ((-1) * x_0_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_10)) ≤ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_0_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_0_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((t + x_0_9 + ((-1) * x_0_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((t + x_0_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_0_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_9 + ((-1) * x_0_10)) ≥ 0) ↔ (((1) * x_0_10 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_0_9) + x_0_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_10 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_0_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1465 (t x_3_7 x_3_9 x_4_7 x_6_7 x_7_9 x_9_10 : ℝ) : (¬ ((t + x_4_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory1466 (t x_6_10 x_6_7 x_7_10 : ℝ) : ((((x_6_7 ≤ x_6_10) ∧ (x_6_10 ≤ x_7_10) ∧ ((x_7_10 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_10 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_6_10)) ≤ ((-1) + t))) ∨ ((x_7_10 ≤ x_6_10) ∧ (x_6_10 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_10)) ≤ ((-1) + t)) ∧ ((x_6_10 + ((-1) * x_7_10)) ≤ ((-1) + t)))) ↔ ((((x_6_7 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_6_10 + ((-1) * x_7_10)) ≤ 0) ∧ ((x_6_7 + ((-1) * x_7_10)) ≤ (-1)) ∧ ((t + x_6_7 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + x_6_10 + ((-1) * x_7_10)) ≥ 1)) ∨ (((x_6_10 + ((-1) * x_7_10)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_6_7 + ((-1) * x_7_10)) ≥ 1) ∧ ((t + ((-1) * x_6_7) + x_6_10) ≥ 1) ∧ ((t + ((-1) * x_6_10) + x_7_10) ≥ 1)))) := by
  classical
  have e0 : ((x_6_10 + ((-1) * x_7_10)) ≤ 0) ↔ (((1) * x_6_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_6_7 + ((-1) * x_7_10)) ≤ (-1)) ↔ (((1) * x_6_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_7 + ((-1) * x_6_10)) ≤ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_6_7 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_6_10 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_7 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_10 ≤ x_7_10) ↔ (((1) * x_6_10 + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_6_10) ↔ (¬ (((1) * x_6_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_6_10 ≤ x_6_7) ↔ (((1) * x_6_10 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_10 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_10 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_10 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_7 + ((-1) * x_7_10)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_6_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_10 + ((-1) * x_7_10)) ≥ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_7_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_6_7 + ((-1) * x_6_10)) ≥ 0) ↔ (((1) * x_6_10 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + ((-1) * x_6_7) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + ((-1) * x_6_10) + x_7_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_7_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1467 (t x_1_10 x_1_4 x_4_10 : ℝ) : ((((x_1_4 ≤ x_1_10) ∧ (x_1_10 ≤ x_4_10) ∧ ((x_4_10 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_10 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_10 + ((-1) * x_1_10)) ≤ ((-1) + t))) ∨ ((x_4_10 ≤ x_1_10) ∧ (x_1_10 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_10)) ≤ ((-1) + t)) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ ((-1) + t)))) ↔ ((((x_1_4 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)))) := by
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
  have e5 : (x_1_4 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_10 ≤ x_4_10) ↔ (((1) * x_1_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_10 ≤ x_1_10) ↔ (¬ (((1) * x_1_10 + (-1) * x_4_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_10 ≤ x_1_4) ↔ (((1) * x_1_10 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_10 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_10 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_10 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_4 + ((-1) * x_1_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_10 + ((-1) * x_4_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_10)) ≤ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ↔ (((1) * x_1_10 + (-1) * x_4_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_4_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1468 (t x_1_10 x_1_4 x_4_10 : ℝ) : ((¬ ((((x_1_4 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((x_1_10 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)))))) ∨ (¬ ((((x_1_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)) ↔ (¬ ((¬ ((x_1_10 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)))))) ∨ (((((x_1_4 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1))) ↔ ((¬ ((¬ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((x_1_10 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_10 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1))))))) := by
  classical
  by_cases h0 : ((((x_1_4 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_4 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((x_1_10 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_1_10 + ((-1) * x_4_10)) ≥ 1)))))
  · by_cases h1 : ((((x_1_10 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)) ↔ (¬ ((¬ ((x_1_10 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_4_10) ≥ 1)))))
    · exact Or.inr (Or.inr (or_congr h0 h1))
    · exact Or.inr (Or.inl h1)
  · exact Or.inl h0

theorem theory1471 (t x_0_2 x_0_4 x_2_3 x_2_4 x_4_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1472 (t x_0_1 x_0_4 x_1_3 x_1_4 x_4_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_4) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1474 (t x_0_3 x_3_6 x_3_7 x_4_6 x_6_7 : ℝ) : (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_3_6) + x_4_6) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1475 (t x_5_7 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_6_7 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x_5_7) + x_6_7) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1476 (t x_3_7 x_5_7 x_5_9 x_7_9 x_9_10 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_3_7 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_5_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1477 (t x_0_4 x_1_7 x_4_7 x_4_8 x_7_8 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1478 (t x_0_2 x_0_7 x_2_3 x_2_7 x_7_9 : ℝ) : (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1479 (t x_0_6 x_1_4 x_4_6 x_4_8 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_6_8)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1480 (t x_2_4 x_3_4 x_3_7 x_4_7 x_7_8 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_7)) ≤ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1481 (t x_0_2 x_0_4 x_2_3 x_2_4 x_4_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_4) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory1482 (x_2_6 x_6_7 : ℝ) : (¬ ((x_2_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1484 (t x_0_1 x_0_9 x_1_9 : ℝ) : ((((x_0_1 ≤ x_0_9) ∧ (x_0_9 ≤ x_1_9) ∧ ((x_1_9 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_1_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_9)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_1_9)) ≤ ((-1) + t)))) ↔ ((((x_0_1 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_9)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_1_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_1_9) ≥ 1)))) := by
  classical
  have e0 : ((x_0_9 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_1) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_1 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_1 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_9) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_0_1 ≤ x_0_9) ↔ (((1) * x_0_1 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_1_9) ↔ (((1) * x_0_9 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_0_9 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_9 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_9 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_1 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_0_1 + ((-1) * x_1_9)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_0_1 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_0_9 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1485 (t x_1_3 x_1_9 x_3_9 : ℝ) : ((((x_1_3 ≤ x_1_9) ∧ (x_1_9 ≤ x_3_9) ∧ ((x_3_9 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_3_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_3_9)) ≤ ((-1) + t)))) ↔ ((((x_1_3 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_3_9) ≥ 1)))) := by
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
  have e5 : (x_1_3 ≤ x_1_9) ↔ (((1) * x_1_3 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_9 ≤ x_3_9) ↔ (((1) * x_1_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : (x_1_9 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_9 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e16 : ((x_1_3 + ((-1) * x_3_9)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e17 : ((t + x_1_3 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e18 : ((t + x_1_9 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18
  all_goals tauto

theorem theory1488 (x_1_9 x_9_10 : ℝ) : (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1⟩
  linarith

theorem theory1489 (t x_0_8 x_1_7 x_2_4 x_4_7 x_4_8 x_7_8 : ℝ) : (¬ ((x_0_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

end ElevenTheory
