import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory3355 (t x_8_10 x_8_9 x_9_10 : ℝ) : (((((x_8_9 + ((-1) * x_8_10)) ≤ 0) ∧ ((x_8_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1) ∧ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_8_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_8_9 + ((-1) * x_8_10)) ≥ 0) ∧ ((x_8_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_8_9) + x_8_10) ≥ 1) ∧ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_8_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_8_10)) ≤ 0)) ∨ (¬ ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1)) ∨ (¬ ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_8_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_8_10)) ≥ 0)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_8_9) + x_8_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_8_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_8_9 + ((-1) * x_8_10)) ≤ 0) ↔ (¬ (((1) * x_8_10 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_8_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_8_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_8_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_8_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_8_9 + ((-1) * x_8_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_8_10 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_8_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_8_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3356 (t x_4_10 x_4_9 x_9_10 : ℝ) : (((((x_4_9 + ((-1) * x_4_10)) ≤ 0) ∧ ((x_4_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_4_9 + ((-1) * x_4_10)) ≥ 1) ∧ ((t + x_4_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_4_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_4_9 + ((-1) * x_4_10)) ≥ 0) ∧ ((x_4_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_4_10) ≥ 1) ∧ ((t + ((-1) * x_4_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_4_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_4_10)) ≤ 0)) ∨ (¬ ((t + x_4_9 + ((-1) * x_4_10)) ≥ 1)) ∨ (¬ ((t + x_4_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_4_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_4_10)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_9) + x_4_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_4_9 + ((-1) * x_4_10)) ≤ 0) ↔ (¬ (((1) * x_4_10 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_4_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_4_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_4_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_4_9 + ((-1) * x_4_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_4_10 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_4_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3358 (t x_0_3 x_1_2 x_1_3 x_3_4 x_3_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3359 (t x_1_6 x_1_7 x_6_7 : ℝ) : (((((x_1_6 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (((x_1_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_6_7) ≥ 1))) ↔ ((¬ ((¬ ((x_1_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((t + x_1_6 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_6) + x_1_7) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_7) + x_6_7) ≥ 1)))))) := by
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
  have e5 : ((x_1_6 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_1_6 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3360 (t x_1_6 x_1_9 x_6_9 : ℝ) : (((((x_1_6 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_1_6 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_6_9) ≥ 1))) ↔ ((¬ ((¬ ((x_1_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((t + x_1_6 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((t + x_1_9 + ((-1) * x_6_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_6) + x_1_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_9) + x_6_9) ≥ 1)))))) := by
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
  have e5 : ((x_1_6 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_1_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_1_6 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3361 (t x_1_6 x_3_5 x_3_6 x_6_7 x_6_9 x_7_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_1_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3362 (t x_2_4 x_2_9 x_4_9 : ℝ) : (((((x_2_4 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_4_9) ≥ 1))) ↔ ((¬ ((¬ ((x_2_9 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((t + x_2_9 + ((-1) * x_4_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_4_9) ≥ 1)))))) := by
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
  have e5 : ((x_2_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_2_4) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_2_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3363 (t x_3_4 x_3_9 x_4_9 : ℝ) : (((((x_3_4 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_3_4 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_3_4) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_4_9) ≥ 1))) ↔ ((¬ ((¬ ((x_3_9 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((t + x_3_4 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((t + x_3_9 + ((-1) * x_4_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_3_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_4) + x_3_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_9) + x_4_9) ≥ 1)))))) := by
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
  have e5 : ((x_3_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_3_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_4 + ((-1) * x_3_9)) ≥ 0) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_3_4) + x_3_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_3_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3364 (t x_0_4 x_0_9 x_4_9 : ℝ) : (((((x_0_4 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_4_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_4_9) ≥ 1))) ↔ ((¬ ((¬ ((x_0_4 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≤ (-1))) ∨ (¬ ((t + x_0_4 + ((-1) * x_0_9)) ≥ 1)) ∨ (¬ ((t + x_0_9 + ((-1) * x_4_9)) ≥ 1)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_4) + x_0_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_9) + x_4_9) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_9)) ≥ 0)))))) := by
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
  have e5 : ((x_0_4 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_9 + ((-1) * x_4_9)) ≥ 0) ↔ (¬ (((1) * x_0_9 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_4 + ((-1) * x_0_9)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_0_4) + x_0_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_0_9) + x_4_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3365 (t x_0_3 x_3_5 x_3_8 x_6_8 x_8_9 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3366 (x_0_3 x_1_3 x_1_5 x_3_5 : ℝ) : (¬ ((x_1_3 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_3_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3367 (t x_0_1 x_1_2 x_1_3 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3368 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3369 (t x_1_3 x_3_5 x_5_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3370 (t x_0_1 x_0_4 x_1_4 : ℝ) : (((((x_0_1 + ((-1) * x_0_4)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_1_4)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1) ∧ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (((x_0_4 + ((-1) * x_1_4)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_4)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_4)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_1_4) ≥ 1))) ↔ ((¬ ((¬ ((x_0_4 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≤ 0)))) ∨ (¬ ((¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_4) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_1_4) ≥ 1)))))) := by
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
  have e7 : ((x_0_1 + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 + ((-1) * x_1_4)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_0_4 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3372 (t x_0_4 x_0_7 x_4_7 : ℝ) : (((((x_0_4 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1))) ↔ ((¬ ((¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((t + x_0_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + x_0_4 + ((-1) * x_0_7)) ≥ 1)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_0_7) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_4_7)) ≥ 0)))))) := by
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
  have e5 : ((x_0_4 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_0_4 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_0_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3373 (t x_0_1 x_0_7 x_1_7 : ℝ) : (((((x_0_1 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_1_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_1_7) ≥ 1))) ↔ ((¬ ((¬ ((x_0_1 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≤ (-1))) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_7)) ≥ 1)) ∨ (¬ ((t + x_0_7 + ((-1) * x_1_7)) ≥ 1)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_1) + x_0_7) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_7) + x_1_7) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_7)) ≥ 0)))))) := by
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
  have e5 : ((x_0_1 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_7 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_1 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_0_1) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_0_7) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3374 (t x_0_1 x_1_3 x_1_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3375 (t x_0_1 x_1_2 x_1_7 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3376 (t x_1_2 x_1_4 x_2_4 : ℝ) : (((((x_1_2 + ((-1) * x_1_4)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_2_4)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1) ∧ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (((x_1_4 + ((-1) * x_2_4)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_4)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1))) ↔ ((¬ ((¬ ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)))) ∨ (¬ ((¬ ((t + ((-1) * x_1_2) + x_1_4) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_2_4)) ≥ 0)))))) := by
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
  have e6 : ((x_1_2 + ((-1) * x_1_4)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 + ((-1) * x_2_4)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_1_2 + ((-1) * x_1_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3377 (t x_0_1 x_1_2 x_1_4 x_2_4 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((t + x_1_4 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory3378 (t x_2_4 x_2_6 x_4_6 : ℝ) : (((((x_2_4 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (((x_2_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_6) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_4_6) ≥ 1))) ↔ ((¬ ((¬ ((x_2_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≤ 0)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_6) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_6) + x_4_6) ≥ 1)))))) := by
  classical
  have e0 : ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_2_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((t + x_2_4 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_2_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_2_4) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_2_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3379 (t x_1_3 x_2_3 x_3_6 x_3_8 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3380 (t x_6_7 x_6_9 x_7_9 : ℝ) : ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ (x_6_9 ≥ 0)) ∨ ((t + x_6_9 + ((-1) * x_7_9)) ≥ 1) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3381 (t x_0_2 x_0_6 x_2_6 : ℝ) : ((t + ((-1) * x_0_6) + x_2_6) ≥ 1) ∨ (¬ (x_0_2 ≥ 0)) ∨ ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3382 (t x_2_7 x_2_9 x_7_9 : ℝ) : (((((x_2_7 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_2_7 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_2_7) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_7_9) ≥ 1))) ↔ ((¬ ((¬ ((x_2_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_2_7 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((t + x_2_7 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((t + x_2_9 + ((-1) * x_7_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_7) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_7_9) ≥ 1)))))) := by
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
  have e5 : ((x_2_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_9 + ((-1) * x_7_9)) ≥ 0) ↔ (¬ (((1) * x_2_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_7 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_2_7) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_2_9) + x_7_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3383 (t x_0_1 x_1_4 x_2_7 x_4_7 x_7_9 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_2_7)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3385 (t x_0_3 x_1_3 x_3_6 x_3_8 x_8_9 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3387 (t x_0_5 x_1_3 x_3_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3388 (t x_0_1 x_0_8 x_1_8 : ℝ) : (((((x_0_1 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_1_8)) ≥ 1)) ∨ (((x_0_8 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_1_8) ≥ 1))) ↔ ((¬ ((¬ ((t + x_0_8 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≤ 0)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≤ (-1))) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≤ 0)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_1) + x_0_8) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_8) + x_1_8) ≥ 1)))))) := by
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
  have e5 : ((x_0_1 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_8 + ((-1) * x_1_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_1 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_0_1) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_0_8) + x_1_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3389 (t x_0_5 x_0_7 x_5_7 x_7_8 : ℝ) : (¬ ((t + x_0_5 + ((-1) * x_0_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory3390 (t x_0_4 x_0_5 x_4_5 : ℝ) : ((t + ((-1) * x_0_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ ((t + ((-1) * x_0_5) + x_4_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3391 (t x_0_5 x_1_3 x_3_5 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3392 (t x_0_1 x_1_4 x_4_8 x_8_9 x_9_10 : ℝ) : (¬ (x_0_1 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3393 (t x_6_10 x_6_9 x_9_10 : ℝ) : (((((x_6_9 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_6_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_6_9 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + x_6_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_6_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_6_9 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_6_9) + x_6_10) ≥ 1) ∧ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_6_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_6_10)) ≤ 0)) ∨ (¬ ((t + x_6_9 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((t + x_6_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_6_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_6_10)) ≥ 0)) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_9) + x_6_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_6_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_6_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_6_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_6_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_6_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_6_9 + ((-1) * x_6_10)) ≥ 0) ↔ (((1) * x_6_10 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_6_9) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_6_10 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_6_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_6_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3394 (t x_0_5 x_1_3 x_3_5 x_5_6 x_6_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_1_3)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3395 (t x_0_3 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3396 (x_0_2 x_0_7 x_2_4 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3397 (t x_0_2 x_0_7 x_2_7 : ℝ) : (((((x_0_2 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_2_7)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_2_7)) ≥ 1)) ∨ (((x_0_7 + ((-1) * x_2_7)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_2_7) ≥ 1))) ↔ ((¬ ((¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_7)) ≥ 1)) ∨ (¬ ((t + x_0_7 + ((-1) * x_2_7)) ≥ 1)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_2) + x_0_7) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_7) + x_2_7) ≥ 1)))))) := by
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
  have e5 : ((x_0_2 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_7 + ((-1) * x_2_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_0_2) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_0_7) + x_2_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3398 (x_0_2 x_0_7 x_1_2 x_2_7 : ℝ) : (¬ ((x_0_2 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3400 (t x_1_3 x_2_3 x_3_4 x_3_8 x_4_8 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ (x_1_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3401 (t x_2_6 x_2_9 x_6_9 : ℝ) : (((((x_2_6 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_2_6 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_2_6) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_6_9) ≥ 1))) ↔ ((¬ ((¬ ((x_2_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((t + x_2_6 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((t + x_2_9 + ((-1) * x_6_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_6) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_6_9) ≥ 1)))))) := by
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
  have e5 : ((x_2_6 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_6 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_2_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_2_6 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_2_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3402 (t x_2_6 x_2_7 x_3_6 x_5_7 x_6_9 x_7_8 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_2_7)) ≥ 0)) ∨ ((t + ((-1) * x_3_6)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3403 (t x_0_2 x_2_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3404 (t x_0_2 x_1_2 x_2_5 x_2_6 x_5_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_5_8 ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3405 (t x_2_5 x_3_5 x_5_6 x_5_8 x_6_7 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3406 (t x_1_2 x_2_3 x_3_6 x_3_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_6 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3407 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_8 : ℝ) : ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_8)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_3_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3408 (t x_0_3 x_3_4 x_3_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3409 (t x_4_5 x_5_6 x_5_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3410 (t x_0_7 x_1_2 x_2_3 x_2_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3411 (t x_0_2 x_2_5 x_2_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3414 (t x_1_3 x_3_5 x_3_6 x_5_6 x_6_8 x_6_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_3_6)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3415 (t x_3_6 x_3_9 x_6_9 : ℝ) : (((((x_3_6 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_3_6 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + x_3_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_3_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_3_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_3_6) + x_3_9) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_6_9) ≥ 1))) ↔ ((¬ ((¬ ((x_3_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((t + x_3_6 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((t + x_3_9 + ((-1) * x_6_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_3_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_3_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_6) + x_3_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_9) + x_6_9) ≥ 1)))))) := by
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
  have e5 : ((x_3_6 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_3_6 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_3_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_3_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_3_6 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_3_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3417 (t x_0_3 x_1_3 x_2_3 x_3_4 x_3_7 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_1_3)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3418 (t x_0_3 x_1_3 x_3_4 x_3_6 x_6_7 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3419 (t x_0_2 x_2_4 x_4_5 x_5_6 x_6_7 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3420 (t x_0_2 x_2_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ (x_9_10 ≥ 0)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3421 (t x_0_2 x_0_5 x_5_6 x_6_9 x_8_9 x_9_10 : ℝ) : (¬ (x_8_9 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_6_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3422 (t x_0_3 x_2_3 x_3_4 x_3_5 x_4_8 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_4_8)) ≤ 0) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3424 (t x_3_10 x_3_9 x_9_10 : ℝ) : (((((x_3_9 + ((-1) * x_3_10)) ≤ 0) ∧ ((x_3_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_3_9 + ((-1) * x_3_10)) ≥ 1) ∧ ((t + x_3_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_3_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_3_9 + ((-1) * x_3_10)) ≥ 0) ∧ ((x_3_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_3_9) + x_3_10) ≥ 1) ∧ ((t + ((-1) * x_3_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_3_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_3_9 + ((-1) * x_3_10)) ≤ 0)) ∨ (¬ ((t + x_3_9 + ((-1) * x_3_10)) ≥ 1)) ∨ (¬ ((t + x_3_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_3_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_3_10)) ≥ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_9) + x_3_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_3_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_3_9 + ((-1) * x_3_10)) ≤ 0) ↔ (¬ (((1) * x_3_10 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_3_10 + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * x_3_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_9 + ((-1) * x_9_10)) ≤ (-1)) ↔ (((1) * x_3_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_3_9 + ((-1) * x_3_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_3_10 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_3_10 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_3_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3426 (t x_0_7 x_0_9 x_7_9 : ℝ) : (((((x_0_7 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_0_7 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_7_9) ≥ 1))) ↔ ((¬ ((¬ ((x_0_7 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((t + x_0_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + x_0_7 + ((-1) * x_0_9)) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_7_9)) ≤ 0)))) ∨ (¬ ((¬ ((x_0_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_9) + x_7_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_7) + x_0_9) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≥ 1)))))) := by
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
  have e5 : ((x_0_7 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_0_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_0_7 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_0_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3427 (t x_0_7 x_3_7 x_6_7 x_7_8 x_7_9 : ℝ) : ((t + ((-1) * x_3_7)) ≤ 0) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3428 (t x_1_7 x_1_8 x_7_8 : ℝ) : (((((x_1_7 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_7_8)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1)) ∧ ((t + x_1_7 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_7_8)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_7_8) ≥ 1))) ↔ ((¬ ((¬ ((x_1_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≤ 0)) ∨ (¬ ((t + x_1_7 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((t + x_1_8 + ((-1) * x_7_8)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_8 + ((-1) * x_7_8)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_7) + x_1_8) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_8) + x_7_8) ≥ 1)))))) := by
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
  have e8 : ((x_1_8 + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_7 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3429 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((t + ((-1) * x_0_6) + x_4_6) ≥ 1) ∨ ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3430 (t x_1_2 x_2_4 x_2_6 x_4_6 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ (x_2_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + x_2_6 + ((-1) * x_4_6)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory3431 (t x_1_2 x_1_8 x_2_8 : ℝ) : (((((x_1_2 + ((-1) * x_1_8)) ≤ 0) ∧ ((x_1_8 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1) ∧ ((t + x_1_8 + ((-1) * x_2_8)) ≥ 1)) ∨ (((x_1_8 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_8)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_8) ≥ 1) ∧ ((t + ((-1) * x_1_8) + x_2_8) ≥ 1))) ↔ ((¬ ((¬ ((t + x_1_8 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((x_1_8 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_8)) ≤ 0)))) ∨ (¬ ((¬ ((t + ((-1) * x_1_2) + x_1_8) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_8) + x_2_8) ≥ 1)) ∨ (¬ ((x_1_8 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_8)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)))))) := by
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
  have e5 : ((x_1_2 + ((-1) * x_1_8)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_8 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_1_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 + ((-1) * x_2_8)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_1_2 + ((-1) * x_1_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_8 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3433 (t x_0_3 x_2_3 x_3_5 x_3_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3434 (t x_0_1 x_0_2 x_1_2 x_2_4 x_2_7 x_7_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ (x_0_1 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3435 (t x_0_5 x_2_5 x_5_6 x_5_7 x_6_7 x_7_9 : ℝ) : (¬ ((x_5_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_0_5)) ≤ 0) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3436 (t x_1_2 x_2_4 x_3_4 : ℝ) : ((t + ((-1) * x_1_2)) ≤ 0) ∨ (¬ (x_3_4 ≥ 0)) ∨ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3437 (x_0_2 x_0_7 x_1_2 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_1_2)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_2_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3440 (t x_0_4 x_4_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_0_4 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3441 (t x_0_1 x_1_3 x_3_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3443 (t x_0_4 x_2_4 x_3_4 x_4_5 x_4_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ (x_3_4 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3444 (t x_0_4 x_1_4 x_4_5 x_4_7 x_5_6 x_6_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3446 (t x_0_4 x_1_2 x_1_4 x_2_4 x_4_5 x_4_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_4)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3448 (t x_1_4 x_4_5 x_4_6 x_5_6 x_6_8 x_6_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3449 (x_0_5 x_1_5 x_1_7 x_5_7 : ℝ) : (¬ ((x_1_5 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3452 (t x_0_3 x_1_3 x_3_5 x_3_7 x_4_5 x_5_7 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3453 (x_0_3 x_0_4 x_0_5 : ℝ) : (¬ ((x_0_4 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ ((x_0_3 + ((-1) * x_0_5)) ≥ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory3454 (t x_0_4 x_4_6 x_5_6 x_6_7 x_6_9 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3455 (t x_4_6 x_4_9 x_6_9 : ℝ) : (((((x_4_6 + ((-1) * x_4_9)) ≤ 0) ∧ ((x_4_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_4_6 + ((-1) * x_4_9)) ≥ 1) ∧ ((t + x_4_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_4_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_4_9)) ≥ 0) ∧ ((x_4_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_4_6) + x_4_9) ≥ 1) ∧ ((t + ((-1) * x_4_9) + x_6_9) ≥ 1))) ↔ ((¬ ((¬ ((x_4_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_9)) ≤ 0)) ∨ (¬ ((t + x_4_6 + ((-1) * x_4_9)) ≥ 1)) ∨ (¬ ((t + x_4_9 + ((-1) * x_6_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_4_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_9)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_6) + x_4_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_4_9) + x_6_9) ≥ 1)))))) := by
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
  have e6 : ((x_4_6 + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * x_4_6 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_4_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_4_6 + ((-1) * x_4_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_4_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3457 (t x_0_1 x_1_2 x_2_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3458 (t x_0_3 x_3_4 x_3_6 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3459 (t x_0_1 x_1_4 x_4_5 x_5_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3460 (t x_0_4 x_1_4 x_4_5 x_4_8 x_5_8 x_8_9 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3462 (t x_5_6 x_5_8 x_6_8 : ℝ) : (¬ (x_6_8 ≥ 0)) ∨ ((t + ((-1) * x_5_8)) ≤ 0) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + x_5_6 + ((-1) * x_5_8)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3463 (t x_0_5 x_5_8 x_6_7 x_7_8 x_8_9 : ℝ) : (¬ (x_0_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_6_7)) ≤ 0) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3464 (t x_0_3 x_1_2 x_2_3 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3465 (t x_0_3 x_1_2 x_2_3 x_3_5 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3467 (t x_2_4 x_2_5 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_2_5 ≥ 0)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ ((t + ((-1) * x_2_4) + x_2_5) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3469 (t x_2_4 x_3_5 x_4_5 x_4_6 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_3_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3472 (t x_0_1 x_1_2 x_1_4 x_2_4 x_4_8 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ (x_1_4 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3475 (x_0_4 x_1_4 x_1_5 x_4_5 : ℝ) : (¬ ((x_1_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_1_5)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_1_4)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3476 (t x_0_2 x_0_3 x_1_2 x_2_3 x_3_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≤ 0)) ∨ (t ≥ 4) ∨ (¬ ((t + x_0_2 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory3477 (t x_0_2 x_1_2 x_2_4 x_2_5 x_5_6 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3478 (t x_0_1 x_0_2 x_2_4 x_2_5 x_4_5 x_5_6 x_5_7 : ℝ) : (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3479 (t x_0_1 x_1_4 x_4_5 x_5_6 x_6_7 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3480 (t x_0_1 x_1_4 x_3_6 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_3_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3481 (t x_0_6 x_4_5 x_5_6 x_5_7 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3482 (x_0_5 x_2_5 x_5_6 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory3483 (t x_0_6 x_1_2 x_2_3 x_2_6 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_3_6)) ≤ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3484 (t x_0_2 x_1_2 x_2_3 x_2_4 x_2_6 : ℝ) : (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_2_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3486 (t x_0_1 x_0_2 x_1_2 x_2_5 x_2_6 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3487 (t x_1_2 x_1_4 x_2_4 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_1_4)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_1_4) + x_2_4) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3488 (t x_0_2 x_1_2 x_2_3 x_2_4 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3493 (t x_0_2 x_1_2 x_2_4 x_2_6 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3494 (t x_0_3 x_3_5 x_3_6 x_6_8 x_8_9 : ℝ) : (¬ (x_3_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3496 (t x_0_6 x_3_6 x_6_7 x_6_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_0_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3497 (t x_4_5 x_5_6 x_6_7 x_7_8 x_8_9 : ℝ) : ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ (x_4_5 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3498 (t x_0_3 x_3_6 x_6_8 x_7_8 x_8_9 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3502 (t x_0_4 x_1_2 x_2_4 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_4 + ((-1) * x_2_4)) ≥ 0)) ∨ (¬ (x_1_2 ≥ 0)) ∨ ((t + ((-1) * x_7_8)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3503 (x_0_7 x_0_8 x_5_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_7_8)) ≤ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_0_8)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3504 (t x_0_1 x_0_2 x_1_2 x_2_4 x_2_5 x_4_5 x_5_7 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_4_5)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3506 (t x_0_3 x_3_4 x_3_6 x_6_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_3_4 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3510 (t x_0_5 x_4_5 x_5_6 x_5_7 x_7_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3511 (t x_1_2 x_1_9 x_2_9 : ℝ) : (((((x_1_2 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_9)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_2_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_2_9) ≥ 1))) ↔ ((¬ ((¬ ((t + x_1_9 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≤ (-1))) ∨ (¬ ((t + x_1_2 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_9)) ≤ 0)))) ∨ (¬ ((¬ ((t + ((-1) * x_1_9) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_9) ≥ 1)) ∨ (¬ ((x_1_9 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_1_9)) ≥ 0)))))) := by
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
  have e5 : ((x_1_2 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_9 + ((-1) * x_2_9)) ≥ 0) ↔ (¬ (((1) * x_1_9 + (-1) * x_2_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 + ((-1) * x_1_9)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_1_2) + x_1_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_1_9) + x_2_9) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3512 (t x_2_8 x_2_9 x_8_9 : ℝ) : (((((x_2_8 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_8_9)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1)) ∧ ((t + x_2_8 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_8_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_8_9)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_8_9) ≥ 1))) ↔ ((¬ ((¬ ((x_2_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_2_8 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((t + x_2_8 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((t + x_2_9 + ((-1) * x_8_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_8) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_8_9) ≥ 1)))))) := by
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
  have e5 : ((x_2_8 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_9 + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_8 + ((-1) * x_8_9)) ≤ (-1)) ↔ (((1) * x_2_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_2_8 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_2_9 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3515 (t x_1_7 x_1_9 x_7_9 : ℝ) : (((((x_1_7 + ((-1) * x_1_9)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_7_9)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1)) ∧ ((t + x_1_7 + ((-1) * x_1_9)) ≥ 1) ∧ ((t + x_1_9 + ((-1) * x_7_9)) ≥ 1)) ∨ (((x_1_9 + ((-1) * x_7_9)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_1_9)) ≥ 0) ∧ ((x_1_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_1_9) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_7_9) ≥ 1))) ↔ ((¬ ((¬ ((x_1_9 + ((-1) * x_7_9)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ ((x_1_7 + ((-1) * x_1_9)) ≤ 0)) ∨ (¬ ((t + x_1_7 + ((-1) * x_1_9)) ≥ 1)) ∨ (¬ ((t + x_1_9 + ((-1) * x_7_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_9 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_7) + x_1_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_9) + x_7_9) ≥ 1)))))) := by
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
  have e5 : ((x_1_7 + ((-1) * x_1_9)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_9 + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * x_1_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_7 + ((-1) * x_7_9)) ≤ (-1)) ↔ (((1) * x_1_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_1_7 + ((-1) * x_1_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_1_9 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3516 (t x_1_7 x_7_9 x_8_9 : ℝ) : (¬ ((x_1_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_1_7 ≥ 0)) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ ((t + x_7_9 + ((-1) * x_8_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3519 (t x_1_2 x_2_6 x_2_7 x_5_7 x_7_9 : ℝ) : (¬ (x_2_6 ≥ 0)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3522 (t x_0_1 x_1_4 x_4_5 x_5_7 x_7_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3523 (t x_0_2 x_1_2 x_2_4 x_2_5 x_2_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ (x_2_5 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_7)) ≤ (-1))) ∨ ((t + ((-1) * x_2_7)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3525 (t x_0_5 x_3_5 x_5_6 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≤ (-1))) ∨ (¬ (x_0_5 ≥ 0)) ∨ ((t + ((-1) * x_7_9)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3528 (t x_0_1 x_0_2 x_1_2 x_2_4 x_2_8 x_4_8 x_8_9 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_2_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  linarith

theorem theory3529 (t x_2_4 x_2_8 x_4_8 : ℝ) : (((((x_2_4 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_2_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + x_2_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (((x_2_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_2_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_2_4) + x_2_8) ≥ 1) ∧ ((t + ((-1) * x_2_8) + x_4_8) ≥ 1))) ↔ ((¬ ((¬ ((x_2_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((t + x_2_8 + ((-1) * x_4_8)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_4) + x_2_8) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_8) + x_4_8) ≥ 1)))))) := by
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
  have e5 : ((x_2_4 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_2_4 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_2_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_2_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_2_4 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_2_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3530 (t x_0_1 x_1_2 x_2_5 x_5_6 x_6_7 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3533 (t x_0_1 x_1_4 x_4_7 x_5_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3534 (t x_0_3 x_3_5 x_5_6 x_6_8 x_8_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_0_3 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3535 (t x_0_1 x_1_4 x_4_6 x_6_7 x_7_8 : ℝ) : (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3536 (t x_0_1 x_1_4 x_2_4 x_4_5 x_4_6 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3537 (t x_0_1 x_1_2 x_2_4 x_4_6 x_6_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ (x_6_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3539 (t x_0_1 x_1_2 x_2_5 x_5_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3540 (t x_5_6 x_5_8 x_6_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ ((t + ((-1) * x_6_8)) ≤ 0) ∨ (¬ (x_5_8 ≥ 0)) ∨ ((t + ((-1) * x_5_6) + x_5_8) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3541 (t x_0_1 x_1_2 x_2_4 x_4_5 x_5_6 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_2_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3542 (x_0_5 x_3_5 x_5_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory3543 (t x_0_1 x_1_4 x_4_7 x_7_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3544 (t x_0_6 x_0_9 x_6_9 : ℝ) : (((((x_0_6 + ((-1) * x_0_9)) ≤ 0) ∧ ((x_0_9 + ((-1) * x_6_9)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_9)) ≥ 1) ∧ ((t + x_0_9 + ((-1) * x_6_9)) ≥ 1)) ∨ (((x_0_9 + ((-1) * x_6_9)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_9)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_9)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_9) ≥ 1) ∧ ((t + ((-1) * x_0_9) + x_6_9) ≥ 1))) ↔ ((¬ ((¬ ((x_0_6 + ((-1) * x_0_9)) ≤ 0)) ∨ (¬ ((x_0_9 + ((-1) * x_6_9)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((t + x_0_6 + ((-1) * x_0_9)) ≥ 1)) ∨ (¬ ((t + x_0_9 + ((-1) * x_6_9)) ≥ 1)))) ∨ (¬ ((¬ ((t + ((-1) * x_0_9) + x_6_9) ≥ 1)) ∨ (¬ ((x_0_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_9)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_6) + x_0_9) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)))))) := by
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
  have e5 : ((x_0_6 + ((-1) * x_0_9)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_0_9 + ((-1) * x_6_9)) ≤ 0) ↔ (((1) * x_0_9 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_6 + ((-1) * x_6_9)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_0_6 + ((-1) * x_0_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_0_9 + ((-1) * x_6_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3547 (t x_0_1 x_1_4 x_4_8 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_7_8 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3548 (x_0_3 x_3_5 x_3_6 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_6)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory3549 (t x_0_7 x_1_2 x_2_4 x_4_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_7)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3550 (t x_0_1 x_1_2 x_2_3 x_3_4 x_4_6 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) ∨ (t ≥ 4) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3551 (t x_0_3 x_3_4 x_3_5 x_4_5 x_5_6 x_5_7 : ℝ) : (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3552 (t x_0_4 x_3_4 x_4_5 x_4_6 x_5_7 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3553 (t x_0_2 x_2_3 x_3_4 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (¬ (x_5_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3555 (x_0_2 x_0_3 x_2_6 x_3_6 : ℝ) : (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((x_2_6 + ((-1) * x_3_6)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3556 (t x_0_3 x_1_3 x_3_5 x_3_7 x_5_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_5_7)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_7_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3557 (t x_0_4 x_1_7 x_4_5 x_4_7 x_7_8 : ℝ) : (t ≥ 4) ∨ (¬ (x_1_7 ≥ 0)) ∨ (¬ ((x_4_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_7)) ≥ 1)) ∨ ((t + ((-1) * x_4_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3559 (t x_1_3 x_2_3 x_3_4 x_3_5 x_4_6 : ℝ) : ((t + ((-1) * x_2_3)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_3_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_4_6 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3560 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_6 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ (x_3_6 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_3_4)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3561 (t x_0_1 x_1_2 x_2_5 x_4_5 x_5_6 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3563 (t x_0_1 x_0_3 x_1_3 x_3_5 x_3_7 x_7_9 : ℝ) : (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_7_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3564 (t x_2_10 x_2_9 x_9_10 : ℝ) : (((((x_2_9 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_2_9 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_2_9 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_2_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_9 + ((-1) * x_2_10)) ≤ 0)) ∨ (¬ ((t + x_2_9 + ((-1) * x_2_10)) ≥ 1)) ∨ (¬ ((t + x_2_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_2_10)) ≥ 0)) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_2_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_2_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_2_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_9 + ((-1) * x_2_10)) ≥ 0) ↔ (((1) * x_2_10 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_2_9) + x_2_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_2_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3565 (t x_0_1 x_1_2 x_2_5 x_2_9 x_5_9 x_9_10 : ℝ) : (¬ (x_5_9 ≥ 0)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_2_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((x_2_5 + ((-1) * x_2_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3566 (t x_5_10 x_5_9 x_9_10 : ℝ) : (((((x_5_9 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_5_9 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_5_9 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_5_9) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_5_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_5_9 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((t + x_5_9 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + x_5_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_5_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_9) + x_5_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_10) + x_9_10) ≥ 1)))))) := by
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
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3567 (t x_1_4 x_4_6 x_6_8 x_8_9 x_9_10 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ (x_1_4 ≥ 0)) ∨ ((t + ((-1) * x_9_10)) ≤ 0) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_8_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3568 (t x_0_3 x_1_3 x_3_4 x_3_5 x_3_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_3_7 ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_3_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3570 (t x_0_1 x_0_3 x_1_2 x_1_7 x_2_7 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ ((t + x_1_7 + ((-1) * x_2_7)) ≥ 1) ∨ (¬ ((x_1_7 + ((-1) * x_2_7)) ≥ 0)) ∨ ((t + ((-1) * x_0_3)) ≤ 0) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  linarith

theorem theory3571 (t x_7_8 x_7_9 x_8_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ ((t + ((-1) * x_7_8) + x_7_9) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3572 (t x_0_1 x_0_2 x_2_6 x_4_6 x_6_7 x_6_8 : ℝ) : (¬ (x_6_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_0_2)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_8)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3573 (x_0_7 x_7_8 x_7_9 : ℝ) : (¬ ((x_7_8 + ((-1) * x_7_9)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ ((x_0_7 + ((-1) * x_7_9)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory3574 (t x_0_1 x_1_4 x_4_8 x_6_8 x_8_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_6_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≥ 1)) ∨ (¬ (x_6_8 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3575 (t x_0_1 x_1_2 x_2_6 x_6_7 x_7_9 : ℝ) : (¬ ((x_1_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_6_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3576 (t x_0_2 x_1_2 x_1_6 x_2_4 x_4_6 x_6_7 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ (x_4_6 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_6)) ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_1_6 + ((-1) * x_6_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3577 (t x_0_5 x_1_2 x_2_5 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3578 (t x_0_5 x_1_2 x_2_5 x_3_5 x_5_6 x_5_8 : ℝ) : ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3579 (t x_0_2 x_1_2 x_2_4 x_2_7 x_4_7 x_7_9 : ℝ) : (¬ ((x_4_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_2_7 + ((-1) * x_4_7)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3580 (t x_0_1 x_1_2 x_2_7 x_4_7 x_7_9 : ℝ) : (¬ (x_4_7 ≥ 0)) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_2_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ (¬ ((x_4_7 + ((-1) * x_7_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3582 (t x_0_1 x_0_6 x_1_2 x_2_6 x_2_7 x_6_9 : ℝ) : (¬ (x_2_7 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3583 (t x_0_3 x_3_5 x_5_7 x_7_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_7_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3584 (t x_0_3 x_2_5 x_3_5 x_5_6 x_5_8 : ℝ) : (¬ (x_0_3 ≥ 0)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3585 (t x_0_3 x_2_3 x_3_4 x_3_5 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ (x_0_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3586 (t x_0_3 x_2_3 x_3_5 x_3_6 x_5_7 : ℝ) : (t ≥ 4) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1))) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3587 (t x_0_2 x_2_4 x_3_4 x_4_6 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≥ 1)) ∨ ((t + ((-1) * x_0_2)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3588 (t x_2_4 x_3_4 x_4_5 : ℝ) : (¬ (x_4_5 ≥ 0)) ∨ ((t + ((-1) * x_2_4) + x_3_4) ≥ 1) ∨ (¬ ((x_3_4 + ((-1) * x_4_5)) ≥ 1)) ∨ ((t + ((-1) * x_2_4)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3590 (t x_0_3 x_2_3 x_3_6 x_3_8 x_8_9 : ℝ) : (t ≥ 4) ∨ (¬ ((x_3_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≥ 1)) ∨ (¬ ((x_2_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ ((x_0_3 + ((-1) * x_3_8)) ≤ (-1))) ∨ (¬ (x_2_3 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3592 (x_0_6 x_0_7 x_5_6 x_6_7 : ℝ) : (¬ ((x_0_6 + ((-1) * x_5_6)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3594 (t x_1_10 x_1_9 x_9_10 : ℝ) : (((((x_1_9 + ((-1) * x_1_10)) ≤ 0) ∧ ((x_1_10 + ((-1) * x_9_10)) ≤ 0) ∧ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1)) ∧ ((t + x_1_9 + ((-1) * x_1_10)) ≥ 1) ∧ ((t + x_1_10 + ((-1) * x_9_10)) ≥ 1)) ∨ (((x_1_10 + ((-1) * x_9_10)) ≥ 0) ∧ ((x_1_9 + ((-1) * x_1_10)) ≥ 0) ∧ ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((t + ((-1) * x_1_9) + x_1_10) ≥ 1) ∧ ((t + ((-1) * x_1_10) + x_9_10) ≥ 1))) ↔ ((¬ ((¬ ((x_1_10 + ((-1) * x_9_10)) ≤ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≤ (-1))) ∨ (¬ ((x_1_9 + ((-1) * x_1_10)) ≤ 0)) ∨ (¬ ((t + x_1_9 + ((-1) * x_1_10)) ≥ 1)) ∨ (¬ ((t + x_1_10 + ((-1) * x_9_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_1_10 + ((-1) * x_9_10)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_1_10)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_9) + x_1_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_10) + x_9_10) ≥ 1)))))) := by
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
  have e5 : ((x_1_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_1_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_1_10 + ((-1) * x_9_10)) ≥ 0) ↔ (¬ (((1) * x_1_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_9 + ((-1) * x_1_10)) ≥ 0) ↔ (((1) * x_1_10 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_1_9) + x_1_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_10 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_1_10) + x_9_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3595 (t x_0_4 x_1_4 x_1_9 x_4_5 x_4_9 x_9_10 : ℝ) : ((t + ((-1) * x_0_4)) ≤ 0) ∨ (¬ ((x_1_4 + ((-1) * x_1_9)) ≥ 0)) ∨ (¬ ((x_1_9 + ((-1) * x_9_10)) ≥ 1)) ∨ (¬ (x_4_9 ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_9 + ((-1) * x_9_10)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3599 (t x_2_10 x_2_5 x_5_10 : ℝ) : (((((x_2_5 + ((-1) * x_2_10)) ≤ 0) ∧ ((x_2_10 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_2_5 + ((-1) * x_5_10)) ≤ (-1)) ∧ ((t + x_2_5 + ((-1) * x_2_10)) ≥ 1) ∧ ((t + x_2_10 + ((-1) * x_5_10)) ≥ 1)) ∨ (((x_2_10 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_2_10)) ≥ 0) ∧ ((x_2_5 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + ((-1) * x_2_5) + x_2_10) ≥ 1) ∧ ((t + ((-1) * x_2_10) + x_5_10) ≥ 1))) ↔ ((¬ ((¬ ((x_2_10 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_10)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_2_10)) ≤ 0)) ∨ (¬ ((t + x_2_5 + ((-1) * x_2_10)) ≥ 1)) ∨ (¬ ((t + x_2_10 + ((-1) * x_5_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_10 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_2_10)) ≥ 0)) ∨ (¬ ((x_2_5 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_5) + x_2_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_10) + x_5_10) ≥ 1)))))) := by
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
  have e5 : ((x_2_5 + ((-1) * x_2_10)) ≤ 0) ↔ (¬ (((1) * x_2_10 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_10 + ((-1) * x_5_10)) ≤ 0) ↔ (((1) * x_2_10 + (-1) * x_5_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_5 + ((-1) * x_5_10)) ≤ (-1)) ↔ (((1) * x_2_5 + (-1) * x_5_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_2_5 + ((-1) * x_2_10)) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_2_10 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_2_10 + ((-1) * x_5_10)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_10 + (-1) * x_5_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3601 (t x_5_10 x_5_6 x_6_10 : ℝ) : (((((x_5_6 + ((-1) * x_5_10)) ≤ 0) ∧ ((x_5_10 + ((-1) * x_6_10)) ≤ 0) ∧ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1)) ∧ ((t + x_5_6 + ((-1) * x_5_10)) ≥ 1) ∧ ((t + x_5_10 + ((-1) * x_6_10)) ≥ 1)) ∨ (((x_5_10 + ((-1) * x_6_10)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_5_10)) ≥ 0) ∧ ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ∧ ((t + ((-1) * x_5_6) + x_5_10) ≥ 1) ∧ ((t + ((-1) * x_5_10) + x_6_10) ≥ 1))) ↔ ((¬ ((¬ ((x_5_10 + ((-1) * x_6_10)) ≤ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≤ (-1))) ∨ (¬ ((x_5_6 + ((-1) * x_5_10)) ≤ 0)) ∨ (¬ ((t + x_5_6 + ((-1) * x_5_10)) ≥ 1)) ∨ (¬ ((t + x_5_10 + ((-1) * x_6_10)) ≥ 1)))) ∨ (¬ ((¬ ((x_5_10 + ((-1) * x_6_10)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_5_10)) ≥ 0)) ∨ (¬ ((x_5_6 + ((-1) * x_6_10)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_6) + x_5_10) ≥ 1)) ∨ (¬ ((t + ((-1) * x_5_10) + x_6_10) ≥ 1)))))) := by
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
  have e5 : ((x_5_6 + ((-1) * x_6_10)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_5_10 + ((-1) * x_6_10)) ≥ 0) ↔ (¬ (((1) * x_5_10 + (-1) * x_6_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_6 + ((-1) * x_5_10)) ≥ 0) ↔ (((1) * x_5_10 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + ((-1) * x_5_6) + x_5_10) ≥ 1) ↔ (¬ (((1) * t + (1) * x_5_10 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + ((-1) * x_5_10) + x_6_10) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_5_10 + (1) * x_6_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3603 (t x_0_1 x_1_2 x_2_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_2_5 + ((-1) * x_5_8)) ≥ 1)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_8_9 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3605 (t x_0_2 x_2_5 x_4_5 : ℝ) : ((t + ((-1) * x_2_5) + x_4_5) ≥ 1) ∨ ((t + ((-1) * x_0_2)) ≤ 0) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ (x_4_5 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3606 (t x_0_4 x_2_4 x_4_5 x_4_6 x_4_7 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ (x_4_7 ≥ 0)) ∨ (¬ ((x_2_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ ((t + ((-1) * x_4_5)) ≤ 0) ∨ (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3607 (t x_0_1 x_1_4 x_4_5 x_5_7 x_7_9 : ℝ) : (¬ ((x_0_1 + ((-1) * x_1_4)) ≥ 1)) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ (x_7_9 ≥ 0)) ∨ (t ≥ 4) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_5)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3608 (t x_0_1 x_1_2 x_2_5 x_5_7 x_7_9 : ℝ) : ((t + ((-1) * x_0_1)) ≤ 0) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_7)) ≥ 1)) ∨ (¬ ((x_5_7 + ((-1) * x_7_9)) ≥ 1)) ∨ (¬ (x_7_9 ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_2)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3609 (t x_3_5 x_5_6 x_5_7 : ℝ) : ((t + ((-1) * x_3_5)) ≤ 0) ∨ (¬ (x_5_6 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + x_5_6 + ((-1) * x_5_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3610 (t x_0_2 x_2_5 x_2_6 x_5_7 x_6_7 x_7_8 : ℝ) : ((t + ((-1) * x_0_2)) ≤ 0) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ (x_5_7 ≥ 0)) ∨ (¬ ((x_5_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  linarith

theorem theory3611 (x_0_5 x_0_6 x_0_7 x_5_7 x_6_7 : ℝ) : (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (¬ ((x_5_7 + ((-1) * x_6_7)) ≤ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory3613 (t x_0_2 x_2_4 x_2_5 x_4_5 : ℝ) : (¬ ((x_2_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) ∨ ((t + ((-1) * x_2_5) + x_4_5) ≥ 1) ∨ ((t + ((-1) * x_2_5)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  linarith

theorem theory3615 (t x_0_2 x_2_5 x_3_5 x_5_6 x_5_7 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≥ 1)) ∨ ((t + ((-1) * x_5_7)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_7)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3616 (x_3_6 x_4_6 x_4_9 x_6_9 : ℝ) : (¬ ((x_3_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_9 + ((-1) * x_6_9)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_4_9)) ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3617 (t x_2_3 x_2_9 x_3_9 : ℝ) : (((((x_2_3 + ((-1) * x_2_9)) ≤ 0) ∧ ((x_2_9 + ((-1) * x_3_9)) ≤ 0) ∧ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1)) ∧ ((t + x_2_3 + ((-1) * x_2_9)) ≥ 1) ∧ ((t + x_2_9 + ((-1) * x_3_9)) ≥ 1)) ∨ (((x_2_9 + ((-1) * x_3_9)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_2_9)) ≥ 0) ∧ ((x_2_3 + ((-1) * x_3_9)) ≥ 1) ∧ ((t + ((-1) * x_2_3) + x_2_9) ≥ 1) ∧ ((t + ((-1) * x_2_9) + x_3_9) ≥ 1))) ↔ ((¬ ((¬ ((x_2_9 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_2_9)) ≤ 0)) ∨ (¬ ((t + x_2_3 + ((-1) * x_2_9)) ≥ 1)) ∨ (¬ ((t + x_2_9 + ((-1) * x_3_9)) ≥ 1)))) ∨ (¬ ((¬ ((x_2_9 + ((-1) * x_3_9)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_2_9)) ≥ 0)) ∨ (¬ ((x_2_3 + ((-1) * x_3_9)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_3) + x_2_9) ≥ 1)) ∨ (¬ ((t + ((-1) * x_2_9) + x_3_9) ≥ 1)))))) := by
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
  have e5 : ((x_2_3 + ((-1) * x_2_9)) ≤ 0) ↔ (((1) * x_2_3 + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : ((x_2_9 + ((-1) * x_3_9)) ≤ 0) ↔ (((1) * x_2_9 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_3 + ((-1) * x_3_9)) ≤ (-1)) ↔ (((1) * x_2_3 + (-1) * x_3_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((t + x_2_3 + ((-1) * x_2_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((t + x_2_9 + ((-1) * x_3_9)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_2_9 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  all_goals tauto

theorem theory3618 (x_0_8 x_3_8 x_3_9 x_8_9 : ℝ) : (¬ ((x_3_8 + ((-1) * x_3_9)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_3_8)) ≤ 0)) ∨ (¬ ((x_3_9 + ((-1) * x_8_9)) ≤ 0)) ∨ (¬ ((x_0_8 + ((-1) * x_8_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3619 (t x_0_5 x_1_2 x_2_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_0_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_2_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ (x_1_2 ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_5_8)) ≥ 1)) ∨ ((t + ((-1) * x_5_6)) ≤ 0) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3620 (t x_0_2 x_2_3 x_3_5 x_5_8 x_8_9 : ℝ) : (¬ ((x_3_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ ((t + ((-1) * x_8_9)) ≤ 0) ∨ (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_8_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_2_3 + ((-1) * x_3_5)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3623 (t x_0_6 x_4_5 x_5_6 x_5_7 x_6_9 : ℝ) : (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + ((-1) * x_0_6)) ≤ 0) ∨ (¬ ((x_0_6 + ((-1) * x_6_9)) ≥ 1)) ∨ (¬ ((x_5_6 + ((-1) * x_6_9)) ≤ (-1))) ∨ (t ≥ 4) ∨ (¬ ((x_4_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ (x_5_7 ≥ 0)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

theorem theory3624 (t x_4_5 x_4_7 x_5_7 : ℝ) : (¬ (x_5_7 ≥ 0)) ∨ ((t + ((-1) * x_4_7)) ≤ 0) ∨ (¬ ((x_4_5 + ((-1) * x_5_7)) ≥ 1)) ∨ ((t + x_4_5 + ((-1) * x_4_7)) ≥ 1) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory3625 (t x_0_2 x_2_5 x_3_5 x_5_6 x_5_9 : ℝ) : (¬ (x_0_2 ≥ 0)) ∨ (¬ ((x_3_5 + ((-1) * x_5_6)) ≤ (-1))) ∨ (¬ ((x_2_5 + ((-1) * x_5_9)) ≤ (-1))) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (t ≥ 4) ∨ ((t + ((-1) * x_5_6)) ≤ 0) ∨ (¬ ((x_3_5 + ((-1) * x_5_9)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  linarith

end ElevenTheory
