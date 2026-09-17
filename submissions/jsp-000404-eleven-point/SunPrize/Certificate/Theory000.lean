import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace ElevenTheory

theorem theory0 (t : ℝ) : ((t < 4) ↔ (¬ (4 ≤ t))) := by
  classical
  have e0 : (t < 4) ↔ (((1) * t + (-4)) < 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (4 ≤ t) ↔ (¬ (((1) * t + (-4)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory1 (t : ℝ) : ((¬ (4 ≤ t)) ↔ (¬ (t ≥ 4))) := by
  classical
  have e0 : (4 ≤ t) ↔ (¬ (((1) * t + (-4)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≥ 4) ↔ (¬ (((1) * t + (-4)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory2 (t x_1_2 : ℝ) : ((x_1_2 < t) ↔ (¬ (t ≤ x_1_2))) := by
  classical
  have e0 : (x_1_2 < t) ↔ (¬ (((1) * t + (-1) * x_1_2) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_2) ↔ (((1) * t + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory3 (t x_0_5 : ℝ) : ((x_0_5 < t) ↔ (¬ (t ≤ x_0_5))) := by
  classical
  have e0 : (x_0_5 < t) ↔ (¬ (((1) * t + (-1) * x_0_5) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_5) ↔ (((1) * t + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory4 (t x_6_8 : ℝ) : ((x_6_8 < t) ↔ (¬ (t ≤ x_6_8))) := by
  classical
  have e0 : (x_6_8 < t) ↔ (¬ (((1) * t + (-1) * x_6_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_6_8) ↔ (((1) * t + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory5 (t x_4_5 : ℝ) : ((x_4_5 < t) ↔ (¬ (t ≤ x_4_5))) := by
  classical
  have e0 : (x_4_5 < t) ↔ (¬ (((1) * t + (-1) * x_4_5) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_4_5) ↔ (((1) * t + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory6 (t x_0_4 : ℝ) : ((x_0_4 < t) ↔ (¬ (t ≤ x_0_4))) := by
  classical
  have e0 : (x_0_4 < t) ↔ (¬ (((1) * t + (-1) * x_0_4) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_4) ↔ (((1) * t + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory7 (t x_3_6 : ℝ) : ((x_3_6 < t) ↔ (¬ (t ≤ x_3_6))) := by
  classical
  have e0 : (x_3_6 < t) ↔ (¬ (((1) * t + (-1) * x_3_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_6) ↔ (((1) * t + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory8 (t x_0_3 : ℝ) : ((x_0_3 < t) ↔ (¬ (t ≤ x_0_3))) := by
  classical
  have e0 : (x_0_3 < t) ↔ (¬ (((1) * t + (-1) * x_0_3) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_3) ↔ (((1) * t + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory9 (t x_0_6 : ℝ) : ((x_0_6 < t) ↔ (¬ (t ≤ x_0_6))) := by
  classical
  have e0 : (x_0_6 < t) ↔ (¬ (((1) * t + (-1) * x_0_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_6) ↔ (((1) * t + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory10 (t x_3_7 : ℝ) : ((x_3_7 < t) ↔ (¬ (t ≤ x_3_7))) := by
  classical
  have e0 : (x_3_7 < t) ↔ (¬ (((1) * t + (-1) * x_3_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_7) ↔ (((1) * t + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory11 (t x_3_5 : ℝ) : ((x_3_5 < t) ↔ (¬ (t ≤ x_3_5))) := by
  classical
  have e0 : (x_3_5 < t) ↔ (¬ (((1) * t + (-1) * x_3_5) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_5) ↔ (((1) * t + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory12 (t x_1_4 : ℝ) : ((x_1_4 < t) ↔ (¬ (t ≤ x_1_4))) := by
  classical
  have e0 : (x_1_4 < t) ↔ (¬ (((1) * t + (-1) * x_1_4) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_4) ↔ (((1) * t + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory13 (t x_7_9 : ℝ) : ((x_7_9 < t) ↔ (¬ (t ≤ x_7_9))) := by
  classical
  have e0 : (x_7_9 < t) ↔ (¬ (((1) * t + (-1) * x_7_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_7_9) ↔ (((1) * t + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory14 (t x_3_4 : ℝ) : ((x_3_4 < t) ↔ (¬ (t ≤ x_3_4))) := by
  classical
  have e0 : (x_3_4 < t) ↔ (¬ (((1) * t + (-1) * x_3_4) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_4) ↔ (((1) * t + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory15 (t x_0_2 : ℝ) : ((x_0_2 < t) ↔ (¬ (t ≤ x_0_2))) := by
  classical
  have e0 : (x_0_2 < t) ↔ (¬ (((1) * t + (-1) * x_0_2) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_2) ↔ (((1) * t + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory16 (t x_2_3 : ℝ) : ((x_2_3 < t) ↔ (¬ (t ≤ x_2_3))) := by
  classical
  have e0 : (x_2_3 < t) ↔ (¬ (((1) * t + (-1) * x_2_3) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_3) ↔ (((1) * t + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory17 (t x_7_8 : ℝ) : ((x_7_8 < t) ↔ (¬ (t ≤ x_7_8))) := by
  classical
  have e0 : (x_7_8 < t) ↔ (¬ (((1) * t + (-1) * x_7_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_7_8) ↔ (((1) * t + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory18 (t x_1_3 : ℝ) : ((x_1_3 < t) ↔ (¬ (t ≤ x_1_3))) := by
  classical
  have e0 : (x_1_3 < t) ↔ (¬ (((1) * t + (-1) * x_1_3) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_3) ↔ (((1) * t + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory19 (t x_0_1 : ℝ) : ((x_0_1 < t) ↔ (¬ (t ≤ x_0_1))) := by
  classical
  have e0 : (x_0_1 < t) ↔ (¬ (((1) * t + (-1) * x_0_1) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_1) ↔ (((1) * t + (-1) * x_0_1) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory20 (t x_9_10 : ℝ) : ((x_9_10 < t) ↔ (¬ (t ≤ x_9_10))) := by
  classical
  have e0 : (x_9_10 < t) ↔ (¬ (((1) * t + (-1) * x_9_10) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_9_10) ↔ (((1) * t + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory21 (t x_5_6 : ℝ) : ((x_5_6 < t) ↔ (¬ (t ≤ x_5_6))) := by
  classical
  have e0 : (x_5_6 < t) ↔ (¬ (((1) * t + (-1) * x_5_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_5_6) ↔ (((1) * t + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory22 (t x_8_9 : ℝ) : ((x_8_9 < t) ↔ (¬ (t ≤ x_8_9))) := by
  classical
  have e0 : (x_8_9 < t) ↔ (¬ (((1) * t + (-1) * x_8_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_8_9) ↔ (((1) * t + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory23 (t x_2_4 : ℝ) : ((x_2_4 < t) ↔ (¬ (t ≤ x_2_4))) := by
  classical
  have e0 : (x_2_4 < t) ↔ (¬ (((1) * t + (-1) * x_2_4) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_4) ↔ (((1) * t + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory24 (t x_1_5 : ℝ) : ((x_1_5 < t) ↔ (¬ (t ≤ x_1_5))) := by
  classical
  have e0 : (x_1_5 < t) ↔ (¬ (((1) * t + (-1) * x_1_5) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_5) ↔ (((1) * t + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory25 (t x_4_7 : ℝ) : ((x_4_7 < t) ↔ (¬ (t ≤ x_4_7))) := by
  classical
  have e0 : (x_4_7 < t) ↔ (¬ (((1) * t + (-1) * x_4_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_4_7) ↔ (((1) * t + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory26 (t x_5_7 : ℝ) : ((x_5_7 < t) ↔ (¬ (t ≤ x_5_7))) := by
  classical
  have e0 : (x_5_7 < t) ↔ (¬ (((1) * t + (-1) * x_5_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_5_7) ↔ (((1) * t + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory27 (t x_4_9 : ℝ) : ((x_4_9 < t) ↔ (¬ (t ≤ x_4_9))) := by
  classical
  have e0 : (x_4_9 < t) ↔ (¬ (((1) * t + (-1) * x_4_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_4_9) ↔ (((1) * t + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory28 (t x_6_7 : ℝ) : ((x_6_7 < t) ↔ (¬ (t ≤ x_6_7))) := by
  classical
  have e0 : (x_6_7 < t) ↔ (¬ (((1) * t + (-1) * x_6_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_6_7) ↔ (((1) * t + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory29 (t x_4_6 : ℝ) : ((x_4_6 < t) ↔ (¬ (t ≤ x_4_6))) := by
  classical
  have e0 : (x_4_6 < t) ↔ (¬ (((1) * t + (-1) * x_4_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_4_6) ↔ (((1) * t + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory30 (t x_3_8 : ℝ) : ((x_3_8 < t) ↔ (¬ (t ≤ x_3_8))) := by
  classical
  have e0 : (x_3_8 < t) ↔ (¬ (((1) * t + (-1) * x_3_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_8) ↔ (((1) * t + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory31 (t x_5_9 : ℝ) : ((x_5_9 < t) ↔ (¬ (t ≤ x_5_9))) := by
  classical
  have e0 : (x_5_9 < t) ↔ (¬ (((1) * t + (-1) * x_5_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_5_9) ↔ (((1) * t + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory32 (t x_6_9 : ℝ) : ((x_6_9 < t) ↔ (¬ (t ≤ x_6_9))) := by
  classical
  have e0 : (x_6_9 < t) ↔ (¬ (((1) * t + (-1) * x_6_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_6_9) ↔ (((1) * t + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory33 (t x_0_7 : ℝ) : ((x_0_7 < t) ↔ (¬ (t ≤ x_0_7))) := by
  classical
  have e0 : (x_0_7 < t) ↔ (¬ (((1) * t + (-1) * x_0_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_7) ↔ (((1) * t + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory34 (t x_2_7 : ℝ) : ((x_2_7 < t) ↔ (¬ (t ≤ x_2_7))) := by
  classical
  have e0 : (x_2_7 < t) ↔ (¬ (((1) * t + (-1) * x_2_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_7) ↔ (((1) * t + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory35 (t x_1_8 : ℝ) : ((x_1_8 < t) ↔ (¬ (t ≤ x_1_8))) := by
  classical
  have e0 : (x_1_8 < t) ↔ (¬ (((1) * t + (-1) * x_1_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_8) ↔ (((1) * t + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory36 (t x_2_5 : ℝ) : ((x_2_5 < t) ↔ (¬ (t ≤ x_2_5))) := by
  classical
  have e0 : (x_2_5 < t) ↔ (¬ (((1) * t + (-1) * x_2_5) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_5) ↔ (((1) * t + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory37 (t x_4_8 : ℝ) : ((x_4_8 < t) ↔ (¬ (t ≤ x_4_8))) := by
  classical
  have e0 : (x_4_8 < t) ↔ (¬ (((1) * t + (-1) * x_4_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_4_8) ↔ (((1) * t + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory38 (t x_5_8 : ℝ) : ((x_5_8 < t) ↔ (¬ (t ≤ x_5_8))) := by
  classical
  have e0 : (x_5_8 < t) ↔ (¬ (((1) * t + (-1) * x_5_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_5_8) ↔ (((1) * t + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory39 (t x_2_6 : ℝ) : ((x_2_6 < t) ↔ (¬ (t ≤ x_2_6))) := by
  classical
  have e0 : (x_2_6 < t) ↔ (¬ (((1) * t + (-1) * x_2_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_6) ↔ (((1) * t + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory40 (t x_2_9 : ℝ) : ((x_2_9 < t) ↔ (¬ (t ≤ x_2_9))) := by
  classical
  have e0 : (x_2_9 < t) ↔ (¬ (((1) * t + (-1) * x_2_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_9) ↔ (((1) * t + (-1) * x_2_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory41 (t x_1_7 : ℝ) : ((x_1_7 < t) ↔ (¬ (t ≤ x_1_7))) := by
  classical
  have e0 : (x_1_7 < t) ↔ (¬ (((1) * t + (-1) * x_1_7) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_7) ↔ (((1) * t + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory42 (t x_0_9 : ℝ) : ((x_0_9 < t) ↔ (¬ (t ≤ x_0_9))) := by
  classical
  have e0 : (x_0_9 < t) ↔ (¬ (((1) * t + (-1) * x_0_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_9) ↔ (((1) * t + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory43 (t x_1_6 : ℝ) : ((x_1_6 < t) ↔ (¬ (t ≤ x_1_6))) := by
  classical
  have e0 : (x_1_6 < t) ↔ (¬ (((1) * t + (-1) * x_1_6) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_6) ↔ (((1) * t + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory44 (t x_3_9 : ℝ) : ((x_3_9 < t) ↔ (¬ (t ≤ x_3_9))) := by
  classical
  have e0 : (x_3_9 < t) ↔ (¬ (((1) * t + (-1) * x_3_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_3_9) ↔ (((1) * t + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory46 (t x_7_10 : ℝ) : ((x_7_10 < t) ↔ (¬ (t ≤ x_7_10))) := by
  classical
  have e0 : (x_7_10 < t) ↔ (¬ (((1) * t + (-1) * x_7_10) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_7_10) ↔ (((1) * t + (-1) * x_7_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory47 (t x_8_10 : ℝ) : ((x_8_10 < t) ↔ (¬ (t ≤ x_8_10))) := by
  classical
  have e0 : (x_8_10 < t) ↔ (¬ (((1) * t + (-1) * x_8_10) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_8_10) ↔ (((1) * t + (-1) * x_8_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory48 (t x_1_9 : ℝ) : ((x_1_9 < t) ↔ (¬ (t ≤ x_1_9))) := by
  classical
  have e0 : (x_1_9 < t) ↔ (¬ (((1) * t + (-1) * x_1_9) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_1_9) ↔ (((1) * t + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory49 (t x_0_8 : ℝ) : ((x_0_8 < t) ↔ (¬ (t ≤ x_0_8))) := by
  classical
  have e0 : (x_0_8 < t) ↔ (¬ (((1) * t + (-1) * x_0_8) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_0_8) ↔ (((1) * t + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory51 (t x_6_10 : ℝ) : ((x_6_10 < t) ↔ (¬ (t ≤ x_6_10))) := by
  classical
  have e0 : (x_6_10 < t) ↔ (¬ (((1) * t + (-1) * x_6_10) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_6_10) ↔ (((1) * t + (-1) * x_6_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory53 (t x_2_10 : ℝ) : ((x_2_10 < t) ↔ (¬ (t ≤ x_2_10))) := by
  classical
  have e0 : (x_2_10 < t) ↔ (¬ (((1) * t + (-1) * x_2_10) ≤ 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (t ≤ x_2_10) ↔ (((1) * t + (-1) * x_2_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory55 (t x_0_8 x_0_9 x_8_9 : ℝ) : ((((x_0_8 ≤ x_0_9) ∧ (x_0_9 ≤ x_8_9) ∧ ((x_8_9 - x_0_8) ≥ 1) ∧ ((x_0_9 - x_0_8) ≤ (t - 1)) ∧ ((x_8_9 - x_0_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_8) ∧ ((x_0_8 - x_8_9) ≥ 1) ∧ ((x_0_8 - x_0_9) ≤ (t - 1)) ∧ ((x_0_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_0_8 ≤ x_0_9) ∧ (x_0_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_0_8)) ≥ 1) ∧ ((x_0_9 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_0_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_0_9) ∧ (x_0_9 ≤ x_0_8) ∧ ((x_0_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_9)) ≤ ((-1) + t)) ∧ ((x_0_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_8 ≤ x_0_9) ↔ (((1) * x_0_8 + (-1) * x_0_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_9 ≤ x_8_9) ↔ (((1) * x_0_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_8_9 - x_0_8) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_9 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_9 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_8_9 ≤ x_0_9) ↔ (¬ (((1) * x_0_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_9 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_0_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_8 - x_0_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_9 + ((-1) * x_0_8)) ≥ 1) ↔ (((1) * x_0_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_9 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_0_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_8 + ((-1) * x_0_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_0_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory56 (t x_0_2 x_0_8 x_2_8 : ℝ) : ((((x_0_2 ≤ x_0_8) ∧ (x_0_8 ≤ x_2_8) ∧ ((x_2_8 - x_0_2) ≥ 1) ∧ ((x_0_8 - x_0_2) ≤ (t - 1)) ∧ ((x_2_8 - x_0_8) ≤ (t - 1))) ∨ ((x_2_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_2) ∧ ((x_0_2 - x_2_8) ≥ 1) ∧ ((x_0_2 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_2_8) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_8) ∧ (x_0_8 ≤ x_2_8) ∧ ((x_2_8 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_2_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_2_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_2 ≤ x_0_8) ↔ (((1) * x_0_2 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_8 ≤ x_2_8) ↔ (((1) * x_0_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_8 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_8 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_8 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_2_8) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_2 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_8 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory57 (t x_0_2 x_0_8 x_2_8 : ℝ) : ((((x_0_2 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_2_8)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_2_8)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_8 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_2_8)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_8)) ≤ (-1))) ∨ (¬ ((t + x_0_2 + ((-1) * x_0_8)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_8)) ≤ 0))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_8 + ((-1) * x_2_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_2 + ((-1) * x_2_8)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_2 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_8 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory58 (t x_0_2 x_0_8 x_2_8 : ℝ) : ((((x_0_8 + ((-1) * x_2_8)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_2_8) ≥ 1)) ↔ (¬ ((¬ ((x_0_2 + ((-1) * x_2_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_8) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_2_8)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_8)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_8) + x_2_8) ≥ 1))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_8)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_2) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_8 + ((-1) * x_2_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_8) + x_2_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory59 (t x_1_2 : ℝ) : ((¬ (t ≤ x_1_2)) ↔ (¬ ((t + ((-1) * x_1_2)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_2) ↔ (((1) * t + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_2)) ≤ 0) ↔ (((1) * t + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory60 (t x_2_6 x_2_7 x_6_7 : ℝ) : ((((x_2_6 ≤ x_2_7) ∧ (x_2_7 ≤ x_6_7) ∧ ((x_6_7 - x_2_6) ≥ 1) ∧ ((x_2_7 - x_2_6) ≤ (t - 1)) ∧ ((x_6_7 - x_2_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_6) ∧ ((x_2_6 - x_6_7) ≥ 1) ∧ ((x_2_6 - x_2_7) ≤ (t - 1)) ∧ ((x_2_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_2_6 ≤ x_2_7) ∧ (x_2_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_6 ≤ x_2_7) ↔ (((1) * x_2_6 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_7 ≤ x_6_7) ↔ (((1) * x_2_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_2_6) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_7 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_7 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory61 (t x_0_2 x_0_5 x_2_5 : ℝ) : ((((x_0_2 ≤ x_0_5) ∧ (x_0_5 ≤ x_2_5) ∧ ((x_2_5 - x_0_2) ≥ 1) ∧ ((x_0_5 - x_0_2) ≤ (t - 1)) ∧ ((x_2_5 - x_0_5) ≤ (t - 1))) ∨ ((x_2_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_2) ∧ ((x_0_2 - x_2_5) ≥ 1) ∧ ((x_0_2 - x_0_5) ≤ (t - 1)) ∧ ((x_0_5 - x_2_5) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_5) ∧ (x_0_5 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_2_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_2_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_2 ≤ x_0_5) ↔ (((1) * x_0_2 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_5 ≤ x_2_5) ↔ (((1) * x_0_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_5 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 - x_2_5) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_5 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_5 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_5 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory62 (t x_0_2 x_0_5 x_2_5 : ℝ) : ((((x_0_2 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_2_5)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_2 + ((-1) * x_0_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≤ (-1))) ∨ (¬ ((x_0_5 + ((-1) * x_2_5)) ≤ 0))))) := by
  classical
  have e0 : ((t + x_0_2 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_2 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_2_5)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 + ((-1) * x_2_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory63 (t x_0_2 x_0_5 x_2_5 : ℝ) : ((((x_0_5 + ((-1) * x_2_5)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1)) ↔ (¬ ((¬ ((x_0_5 + ((-1) * x_2_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_5) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_5) + x_2_5) ≥ 1))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_5 + ((-1) * x_2_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_2 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_2) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_5) + x_2_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory64 (t x_0_5 : ℝ) : ((¬ (t ≤ x_0_5)) ↔ (¬ ((t + ((-1) * x_0_5)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_5) ↔ (((1) * t + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * t + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory65 (t x_0_5 x_0_6 x_5_6 : ℝ) : ((((x_0_5 ≤ x_0_6) ∧ (x_0_6 ≤ x_5_6) ∧ ((x_5_6 - x_0_5) ≥ 1) ∧ ((x_0_6 - x_0_5) ≤ (t - 1)) ∧ ((x_5_6 - x_0_6) ≤ (t - 1))) ∨ ((x_5_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_5) ∧ ((x_0_5 - x_5_6) ≥ 1) ∧ ((x_0_5 - x_0_6) ≤ (t - 1)) ∧ ((x_0_6 - x_5_6) ≤ (t - 1)))) ↔ (((x_0_5 ≤ x_0_6) ∧ (x_0_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_5_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_5 ≤ x_0_6) ↔ (((1) * x_0_5 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_6 ≤ x_5_6) ↔ (((1) * x_0_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_6 - x_0_5) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_6 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_5 - x_5_6) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_5 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory66 (t x_1_5 x_1_8 x_5_8 : ℝ) : ((((x_1_5 ≤ x_1_8) ∧ (x_1_8 ≤ x_5_8) ∧ ((x_5_8 - x_1_5) ≥ 1) ∧ ((x_1_8 - x_1_5) ≤ (t - 1)) ∧ ((x_5_8 - x_1_8) ≤ (t - 1))) ∨ ((x_5_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_5) ∧ ((x_1_5 - x_5_8) ≥ 1) ∧ ((x_1_5 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_5_8) ≤ (t - 1)))) ↔ (((x_1_5 ≤ x_1_8) ∧ (x_1_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_5_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_5 ≤ x_1_8) ↔ (((1) * x_1_5 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_5_8) ↔ (((1) * x_1_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_8 - x_1_5) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_5 - x_5_8) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_5 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory67 (t x_6_8 : ℝ) : ((¬ (t ≤ x_6_8)) ↔ (¬ ((t + ((-1) * x_6_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_6_8) ↔ (((1) * t + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_6_8)) ≤ 0) ↔ (((1) * t + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory68 (t x_6_7 x_6_8 x_7_8 : ℝ) : ((((x_6_7 ≤ x_6_8) ∧ (x_6_8 ≤ x_7_8) ∧ ((x_7_8 - x_6_7) ≥ 1) ∧ ((x_6_8 - x_6_7) ≤ (t - 1)) ∧ ((x_7_8 - x_6_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_6_8) ∧ (x_6_8 ≤ x_6_7) ∧ ((x_6_7 - x_7_8) ≥ 1) ∧ ((x_6_7 - x_6_8) ≤ (t - 1)) ∧ ((x_6_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_6_7 ≤ x_6_8) ∧ (x_6_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_6_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_6_8) ∧ (x_6_8 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_6_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_7 ≤ x_6_8) ↔ (((1) * x_6_7 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_6_8 ≤ x_7_8) ↔ (((1) * x_6_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 - x_6_7) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_8 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_6_8) ↔ (¬ (((1) * x_6_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_8 ≤ x_6_7) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_7 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_7 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory69 (t x_5_6 x_5_8 x_6_8 : ℝ) : ((((x_5_6 ≤ x_5_8) ∧ (x_5_8 ≤ x_6_8) ∧ ((x_6_8 - x_5_6) ≥ 1) ∧ ((x_5_8 - x_5_6) ≤ (t - 1)) ∧ ((x_6_8 - x_5_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_6) ∧ ((x_5_6 - x_6_8) ≥ 1) ∧ ((x_5_6 - x_5_8) ≤ (t - 1)) ∧ ((x_5_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_5_6 ≤ x_5_8) ∧ (x_5_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_5_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_5_6 ≤ x_5_8) ↔ (((1) * x_5_6 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_8 ≤ x_6_8) ↔ (((1) * x_5_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_8 - x_5_6) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_8 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_8 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_8 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_5_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_6 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_6 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory70 (x_1_5 x_5_6 x_5_8 : ℝ) : (¬ ((x_5_6 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_1_5 + ((-1) * x_5_8)) ≤ (-1))) ∨ (¬ ((x_1_5 + ((-1) * x_5_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory71 (t x_1_5 x_1_6 x_5_6 : ℝ) : ((((x_1_5 ≤ x_1_6) ∧ (x_1_6 ≤ x_5_6) ∧ ((x_5_6 - x_1_5) ≥ 1) ∧ ((x_1_6 - x_1_5) ≤ (t - 1)) ∧ ((x_5_6 - x_1_6) ≤ (t - 1))) ∨ ((x_5_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_5) ∧ ((x_1_5 - x_5_6) ≥ 1) ∧ ((x_1_5 - x_1_6) ≤ (t - 1)) ∧ ((x_1_6 - x_5_6) ≤ (t - 1)))) ↔ (((x_1_5 ≤ x_1_6) ∧ (x_1_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_5_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_1_6) ↔ (((1) * x_1_5 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_6 ≤ x_5_6) ↔ (((1) * x_1_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_6 - x_1_5) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_6 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_6 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_6 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_5 - x_5_6) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory72 (t x_4_5 : ℝ) : ((¬ (t ≤ x_4_5)) ↔ (¬ ((t + ((-1) * x_4_5)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_4_5) ↔ (((1) * t + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_4_5)) ≤ 0) ↔ (((1) * t + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory73 (t x_0_1 x_0_5 x_1_5 : ℝ) : ((((x_0_1 ≤ x_0_5) ∧ (x_0_5 ≤ x_1_5) ∧ ((x_1_5 - x_0_1) ≥ 1) ∧ ((x_0_5 - x_0_1) ≤ (t - 1)) ∧ ((x_1_5 - x_0_5) ≤ (t - 1))) ∨ ((x_1_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_1) ∧ ((x_0_1 - x_1_5) ≥ 1) ∧ ((x_0_1 - x_0_5) ≤ (t - 1)) ∧ ((x_0_5 - x_1_5) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_5) ∧ (x_0_5 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_1_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_1_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_1 ≤ x_0_5) ↔ (((1) * x_0_1 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_5 ≤ x_1_5) ↔ (((1) * x_0_5 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_5 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_5 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_1_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_1 - x_1_5) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_5 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_5 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_5 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_1 + ((-1) * x_1_5)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory74 (t x_0_5 x_0_8 x_5_8 : ℝ) : ((((x_0_5 ≤ x_0_8) ∧ (x_0_8 ≤ x_5_8) ∧ ((x_5_8 - x_0_5) ≥ 1) ∧ ((x_0_8 - x_0_5) ≤ (t - 1)) ∧ ((x_5_8 - x_0_8) ≤ (t - 1))) ∨ ((x_5_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_5) ∧ ((x_0_5 - x_5_8) ≥ 1) ∧ ((x_0_5 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_5_8) ≤ (t - 1)))) ↔ (((x_0_5 ≤ x_0_8) ∧ (x_0_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_5_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_5 ≤ x_0_8) ↔ (((1) * x_0_5 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_8 ≤ x_5_8) ↔ (((1) * x_0_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_8 - x_0_5) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_5 - x_5_8) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_5 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_8 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory75 (t x_0_4 x_0_5 x_4_5 : ℝ) : ((((x_0_4 ≤ x_0_5) ∧ (x_0_5 ≤ x_4_5) ∧ ((x_4_5 - x_0_4) ≥ 1) ∧ ((x_0_5 - x_0_4) ≤ (t - 1)) ∧ ((x_4_5 - x_0_5) ≤ (t - 1))) ∨ ((x_4_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_4) ∧ ((x_0_4 - x_4_5) ≥ 1) ∧ ((x_0_4 - x_0_5) ≤ (t - 1)) ∧ ((x_0_5 - x_4_5) ≤ (t - 1)))) ↔ (((x_0_4 ≤ x_0_5) ∧ (x_0_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_4_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_0_5) ↔ (((1) * x_0_4 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_5 ≤ x_4_5) ↔ (((1) * x_0_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_5 - x_0_4) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_5 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_5 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_4 - x_4_5) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_5 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_5 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_5 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory76 (t x_0_4 : ℝ) : ((¬ (t ≤ x_0_4)) ↔ (¬ ((t + ((-1) * x_0_4)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_4) ↔ (((1) * t + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * t + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory77 (t x_0_1 x_0_3 x_1_3 : ℝ) : ((((x_0_1 ≤ x_0_3) ∧ (x_0_3 ≤ x_1_3) ∧ ((x_1_3 - x_0_1) ≥ 1) ∧ ((x_0_3 - x_0_1) ≤ (t - 1)) ∧ ((x_1_3 - x_0_3) ≤ (t - 1))) ∨ ((x_1_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_1) ∧ ((x_0_1 - x_1_3) ≥ 1) ∧ ((x_0_1 - x_0_3) ≤ (t - 1)) ∧ ((x_0_3 - x_1_3) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_3) ∧ (x_0_3 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_3 + ((-1) * x_0_3)) ≤ ((-1) + t))) ∨ ((x_1_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_0_3 + ((-1) * x_1_3)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_1 ≤ x_0_3) ↔ (((1) * x_0_1 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_3 ≤ x_1_3) ↔ (((1) * x_0_3 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_3 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_3 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_3 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_3 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_1_3) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_1 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_3 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_3 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_3 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_3 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory78 (t x_0_1 x_0_3 x_1_3 : ℝ) : ((((x_0_1 + ((-1) * x_0_3)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_1_3)) ≤ 0) ∧ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1)) ∧ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1) ∧ ((t + x_0_3 + ((-1) * x_1_3)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_3 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≤ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≤ (-1))) ∨ (¬ ((x_0_1 + ((-1) * x_0_3)) ≤ 0)) ∨ (¬ ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_0_3)) ≤ 0) ↔ (((1) * x_0_1 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_3 + ((-1) * x_1_3)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_1 + ((-1) * x_1_3)) ≤ (-1)) ↔ (((1) * x_0_1 + (-1) * x_1_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_1 + ((-1) * x_0_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_3 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory79 (t x_0_1 x_0_3 x_1_3 : ℝ) : ((((x_0_3 + ((-1) * x_1_3)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_0_3)) ≥ 0) ∧ ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ∧ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) ↔ (¬ ((¬ ((x_0_1 + ((-1) * x_0_3)) ≥ 0)) ∨ (¬ ((x_0_1 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_1_3) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_1) + x_0_3) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_1_3)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_1 + ((-1) * x_0_3)) ≥ 0) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_3) + x_1_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_1) + x_0_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_1_3)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory80 (t x_3_7 x_3_8 x_7_8 : ℝ) : ((((x_3_7 ≤ x_3_8) ∧ (x_3_8 ≤ x_7_8) ∧ ((x_7_8 - x_3_7) ≥ 1) ∧ ((x_3_8 - x_3_7) ≤ (t - 1)) ∧ ((x_7_8 - x_3_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_7) ∧ ((x_3_7 - x_7_8) ≥ 1) ∧ ((x_3_7 - x_3_8) ≤ (t - 1)) ∧ ((x_3_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_3_7 ≤ x_3_8) ∧ (x_3_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_7 ≤ x_3_8) ↔ (((1) * x_3_7 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_8 ≤ x_7_8) ↔ (((1) * x_3_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_8 - x_3_7) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_8 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_8 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_7 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_8 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_8 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_7 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory81 (t x_5_6 x_5_7 x_6_7 : ℝ) : ((((x_5_6 ≤ x_5_7) ∧ (x_5_7 ≤ x_6_7) ∧ ((x_6_7 - x_5_6) ≥ 1) ∧ ((x_5_7 - x_5_6) ≤ (t - 1)) ∧ ((x_6_7 - x_5_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_5_7) ∧ (x_5_7 ≤ x_5_6) ∧ ((x_5_6 - x_6_7) ≥ 1) ∧ ((x_5_6 - x_5_7) ≤ (t - 1)) ∧ ((x_5_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_5_6 ≤ x_5_7) ∧ (x_5_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_5_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_5_7) ∧ (x_5_7 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_5_6 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_6 ≤ x_5_7) ↔ (((1) * x_5_6 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_7 ≤ x_6_7) ↔ (((1) * x_5_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_5_6) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_7 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_7 ≤ x_5_6) ↔ (¬ (((1) * x_5_6 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_5_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_6 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_5_6)) ≥ 1) ↔ (((1) * x_5_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_7 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_6 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_6 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_6 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory82 (t x_3_5 x_3_6 x_5_6 : ℝ) : ((((x_3_5 ≤ x_3_6) ∧ (x_3_6 ≤ x_5_6) ∧ ((x_5_6 - x_3_5) ≥ 1) ∧ ((x_3_6 - x_3_5) ≤ (t - 1)) ∧ ((x_5_6 - x_3_6) ≤ (t - 1))) ∨ ((x_5_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_5) ∧ ((x_3_5 - x_5_6) ≥ 1) ∧ ((x_3_5 - x_3_6) ≤ (t - 1)) ∧ ((x_3_6 - x_5_6) ≤ (t - 1)))) ↔ (((x_3_5 ≤ x_3_6) ∧ (x_3_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_3_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_5_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_5 ≤ x_3_6) ↔ (((1) * x_3_5 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_5_6) ↔ (((1) * x_3_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 - x_3_5) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_6 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_6 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_6 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_5 - x_5_6) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_5 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_6 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory83 (t x_3_6 : ℝ) : ((¬ (t ≤ x_3_6)) ↔ (¬ ((t + ((-1) * x_3_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_6) ↔ (((1) * t + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_6)) ≤ 0) ↔ (((1) * t + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory84 (t x_3_6 x_3_7 x_6_7 : ℝ) : ((((x_3_6 ≤ x_3_7) ∧ (x_3_7 ≤ x_6_7) ∧ ((x_6_7 - x_3_6) ≥ 1) ∧ ((x_3_7 - x_3_6) ≤ (t - 1)) ∧ ((x_6_7 - x_3_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_6) ∧ ((x_3_6 - x_6_7) ≥ 1) ∧ ((x_3_6 - x_3_7) ≤ (t - 1)) ∧ ((x_3_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_3_6 ≤ x_3_7) ∧ (x_3_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_3_7) ↔ (((1) * x_3_6 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_7 ≤ x_6_7) ↔ (((1) * x_3_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_3_6) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_7 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory85 (x_3_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_3_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_3_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory86 (t x_0_6 x_0_7 x_6_7 : ℝ) : ((((x_0_6 ≤ x_0_7) ∧ (x_0_7 ≤ x_6_7) ∧ ((x_6_7 - x_0_6) ≥ 1) ∧ ((x_0_7 - x_0_6) ≤ (t - 1)) ∧ ((x_6_7 - x_0_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_6) ∧ ((x_0_6 - x_6_7) ≥ 1) ∧ ((x_0_6 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_0_6 ≤ x_0_7) ∧ (x_0_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_6 ≤ x_0_7) ↔ (((1) * x_0_6 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_7 ≤ x_6_7) ↔ (((1) * x_0_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_0_6) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_7 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_6 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory87 (t x_0_6 x_0_7 x_6_7 : ℝ) : ((((x_0_6 + ((-1) * x_0_7)) ≤ 0) ∧ ((x_0_7 + ((-1) * x_6_7)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1)) ∧ ((t + x_0_6 + ((-1) * x_0_7)) ≥ 1) ∧ ((t + x_0_7 + ((-1) * x_6_7)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_7 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≤ (-1))) ∨ (¬ ((t + x_0_6 + ((-1) * x_0_7)) ≥ 1))))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_0_7)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_7 + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * x_0_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_6 + ((-1) * x_6_7)) ≤ (-1)) ↔ (((1) * x_0_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_6 + ((-1) * x_0_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_7 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory88 (t x_0_6 x_0_7 x_6_7 : ℝ) : ((((x_0_7 + ((-1) * x_6_7)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_0_7)) ≥ 0) ∧ ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_0_7) ≥ 1) ∧ ((t + ((-1) * x_0_7) + x_6_7) ≥ 1)) ↔ (¬ ((¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_6) + x_0_7) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_7) + x_6_7) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_7)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_7 + ((-1) * x_6_7)) ≥ 0) ↔ (¬ (((1) * x_0_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_6) + x_0_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_7) + x_6_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 + ((-1) * x_0_7)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory89 (t x_0_3 : ℝ) : ((¬ (t ≤ x_0_3)) ↔ (¬ ((t + ((-1) * x_0_3)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_3) ↔ (((1) * t + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_3)) ≤ 0) ↔ (((1) * t + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory90 (t x_0_3 x_0_6 x_3_6 : ℝ) : ((((x_0_3 ≤ x_0_6) ∧ (x_0_6 ≤ x_3_6) ∧ ((x_3_6 - x_0_3) ≥ 1) ∧ ((x_0_6 - x_0_3) ≤ (t - 1)) ∧ ((x_3_6 - x_0_6) ≤ (t - 1))) ∨ ((x_3_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_3) ∧ ((x_0_3 - x_3_6) ≥ 1) ∧ ((x_0_3 - x_0_6) ≤ (t - 1)) ∧ ((x_0_6 - x_3_6) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_6) ∧ (x_0_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_3_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_3 ≤ x_0_6) ↔ (((1) * x_0_3 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_6 ≤ x_3_6) ↔ (((1) * x_0_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_6 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_6 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_3_6) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_3 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory91 (t x_0_7 x_0_8 x_7_8 : ℝ) : ((((x_0_7 ≤ x_0_8) ∧ (x_0_8 ≤ x_7_8) ∧ ((x_7_8 - x_0_7) ≥ 1) ∧ ((x_0_8 - x_0_7) ≤ (t - 1)) ∧ ((x_7_8 - x_0_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_7) ∧ ((x_0_7 - x_7_8) ≥ 1) ∧ ((x_0_7 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_0_7 ≤ x_0_8) ∧ (x_0_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_0_7)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_7) ∧ ((x_0_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_7 ≤ x_0_8) ↔ (((1) * x_0_7 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_8 ≤ x_7_8) ↔ (((1) * x_0_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_8 - x_0_7) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_8 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_7 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_8 + ((-1) * x_0_7)) ≥ 1) ↔ (((1) * x_0_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_8 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_0_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_7 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory92 (x_0_7 x_6_7 x_7_8 : ℝ) : (¬ ((x_0_7 + ((-1) * x_6_7)) ≤ 0)) ∨ (¬ ((x_0_7 + ((-1) * x_7_8)) ≥ 1)) ∨ (¬ ((x_6_7 + ((-1) * x_7_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory93 (t x_0_6 : ℝ) : ((¬ (t ≤ x_0_6)) ↔ (¬ ((t + ((-1) * x_0_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_6) ↔ (((1) * t + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * t + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory94 (t x_4_6 x_4_8 x_6_8 : ℝ) : ((((x_4_6 ≤ x_4_8) ∧ (x_4_8 ≤ x_6_8) ∧ ((x_6_8 - x_4_6) ≥ 1) ∧ ((x_4_8 - x_4_6) ≤ (t - 1)) ∧ ((x_6_8 - x_4_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_6) ∧ ((x_4_6 - x_6_8) ≥ 1) ∧ ((x_4_6 - x_4_8) ≤ (t - 1)) ∧ ((x_4_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_4_6 ≤ x_4_8) ∧ (x_4_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_6 ≤ x_4_8) ↔ (((1) * x_4_6 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_8 ≤ x_6_8) ↔ (((1) * x_4_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_8 - x_4_6) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_8 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_6 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory95 (t x_3_7 : ℝ) : ((¬ (t ≤ x_3_7)) ↔ (¬ ((t + ((-1) * x_3_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_7) ↔ (((1) * t + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * t + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory96 (t x_6_8 x_6_9 x_8_9 : ℝ) : ((((x_6_8 ≤ x_6_9) ∧ (x_6_9 ≤ x_8_9) ∧ ((x_8_9 - x_6_8) ≥ 1) ∧ ((x_6_9 - x_6_8) ≤ (t - 1)) ∧ ((x_8_9 - x_6_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_8) ∧ ((x_6_8 - x_8_9) ≥ 1) ∧ ((x_6_8 - x_6_9) ≤ (t - 1)) ∧ ((x_6_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_6_8 ≤ x_6_9) ∧ (x_6_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_6_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_6_8 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_6_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_8 ≤ x_6_9) ↔ (((1) * x_6_8 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_6_9 ≤ x_8_9) ↔ (((1) * x_6_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_6_8) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_9 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_6_9) ↔ (¬ (((1) * x_6_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_6_9 ≤ x_6_8) ↔ (¬ (((1) * x_6_8 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_6_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_8 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_6_8)) ≥ 1) ↔ (((1) * x_6_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_9 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_8 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_8 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_8 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory97 (t x_4_5 x_4_8 x_5_8 : ℝ) : ((((x_4_5 ≤ x_4_8) ∧ (x_4_8 ≤ x_5_8) ∧ ((x_5_8 - x_4_5) ≥ 1) ∧ ((x_4_8 - x_4_5) ≤ (t - 1)) ∧ ((x_5_8 - x_4_8) ≤ (t - 1))) ∨ ((x_5_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_5) ∧ ((x_4_5 - x_5_8) ≥ 1) ∧ ((x_4_5 - x_4_8) ≤ (t - 1)) ∧ ((x_4_8 - x_5_8) ≤ (t - 1)))) ↔ (((x_4_5 ≤ x_4_8) ∧ (x_4_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_5_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_5 ≤ x_4_8) ↔ (((1) * x_4_5 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_8 ≤ x_5_8) ↔ (((1) * x_4_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_8 - x_4_5) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_8 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 - x_5_8) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory98 (t x_0_6 x_0_8 x_6_8 : ℝ) : ((((x_0_6 ≤ x_0_8) ∧ (x_0_8 ≤ x_6_8) ∧ ((x_6_8 - x_0_6) ≥ 1) ∧ ((x_0_8 - x_0_6) ≤ (t - 1)) ∧ ((x_6_8 - x_0_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_6) ∧ ((x_0_6 - x_6_8) ≥ 1) ∧ ((x_0_6 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_0_6 ≤ x_0_8) ∧ (x_0_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_0_6)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_6) ∧ ((x_0_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_6 ≤ x_0_8) ↔ (((1) * x_0_6 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_8 ≤ x_6_8) ↔ (((1) * x_0_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_8 - x_0_6) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_8 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_8 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_0_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_6 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_0_6)) ≥ 1) ↔ (((1) * x_0_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_8 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_6 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory99 (x_0_6 x_4_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_8)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory100 (t x_3_5 : ℝ) : ((¬ (t ≤ x_3_5)) ↔ (¬ ((t + ((-1) * x_3_5)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_5) ↔ (((1) * t + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * t + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory101 (t x_6_7 x_6_9 x_7_9 : ℝ) : ((((x_6_7 ≤ x_6_9) ∧ (x_6_9 ≤ x_7_9) ∧ ((x_7_9 - x_6_7) ≥ 1) ∧ ((x_6_9 - x_6_7) ≤ (t - 1)) ∧ ((x_7_9 - x_6_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_7) ∧ ((x_6_7 - x_7_9) ≥ 1) ∧ ((x_6_7 - x_6_9) ≤ (t - 1)) ∧ ((x_6_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_6_7 ≤ x_6_9) ∧ (x_6_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_6_9 + ((-1) * x_6_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_6_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_6_9) ∧ (x_6_9 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_6_7 + ((-1) * x_6_9)) ≤ ((-1) + t)) ∧ ((x_6_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_6_7 ≤ x_6_9) ↔ (((1) * x_6_7 + (-1) * x_6_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_6_9 ≤ x_7_9) ↔ (((1) * x_6_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_7_9 - x_6_7) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_9 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_9 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_7_9 ≤ x_6_9) ↔ (¬ (((1) * x_6_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_9 ≤ x_6_7) ↔ (¬ (((1) * x_6_7 + (-1) * x_6_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_6_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_6_7 - x_6_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_6_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_9 + ((-1) * x_6_7)) ≥ 1) ↔ (((1) * x_6_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_9 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_7 + (-1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_9 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_6_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_6_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_6_7 + ((-1) * x_6_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_7 + (1) * x_6_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_6_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_6_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory102 (t x_1_4 x_1_5 x_4_5 : ℝ) : ((((x_1_4 ≤ x_1_5) ∧ (x_1_5 ≤ x_4_5) ∧ ((x_4_5 - x_1_4) ≥ 1) ∧ ((x_1_5 - x_1_4) ≤ (t - 1)) ∧ ((x_4_5 - x_1_5) ≤ (t - 1))) ∨ ((x_4_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_4) ∧ ((x_1_4 - x_4_5) ≥ 1) ∧ ((x_1_4 - x_1_5) ≤ (t - 1)) ∧ ((x_1_5 - x_4_5) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_5) ∧ (x_1_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_4_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_4 ≤ x_1_5) ↔ (((1) * x_1_4 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_4_5) ↔ (((1) * x_1_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_5 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_5 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_5 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_5 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_4 - x_4_5) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_5 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory103 (t x_1_4 : ℝ) : ((¬ (t ≤ x_1_4)) ↔ (¬ ((t + ((-1) * x_1_4)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_4) ↔ (((1) * t + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_4)) ≤ 0) ↔ (((1) * t + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory104 (t x_4_7 x_4_9 x_7_9 : ℝ) : ((((x_4_7 ≤ x_4_9) ∧ (x_4_9 ≤ x_7_9) ∧ ((x_7_9 - x_4_7) ≥ 1) ∧ ((x_4_9 - x_4_7) ≤ (t - 1)) ∧ ((x_7_9 - x_4_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_7) ∧ ((x_4_7 - x_7_9) ≥ 1) ∧ ((x_4_7 - x_4_9) ≤ (t - 1)) ∧ ((x_4_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_4_7 ≤ x_4_9) ∧ (x_4_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_7 ≤ x_4_9) ↔ (((1) * x_4_7 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_9 ≤ x_7_9) ↔ (((1) * x_4_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_4_7) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_7 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory105 (t x_4_5 x_4_7 x_5_7 : ℝ) : ((((x_4_5 ≤ x_4_7) ∧ (x_4_7 ≤ x_5_7) ∧ ((x_5_7 - x_4_5) ≥ 1) ∧ ((x_4_7 - x_4_5) ≤ (t - 1)) ∧ ((x_5_7 - x_4_7) ≤ (t - 1))) ∨ ((x_5_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_5) ∧ ((x_4_5 - x_5_7) ≥ 1) ∧ ((x_4_5 - x_4_7) ≤ (t - 1)) ∧ ((x_4_7 - x_5_7) ≤ (t - 1)))) ↔ (((x_4_5 ≤ x_4_7) ∧ (x_4_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_4_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_5_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_4_5 ≤ x_4_7) ↔ (((1) * x_4_5 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_7 ≤ x_5_7) ↔ (((1) * x_4_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_7 - x_4_5) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_7 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_7 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_7 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_4_5 - x_5_7) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_7 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory106 (t x_3_4 x_3_7 x_4_7 : ℝ) : ((((x_3_4 ≤ x_3_7) ∧ (x_3_7 ≤ x_4_7) ∧ ((x_4_7 - x_3_4) ≥ 1) ∧ ((x_3_7 - x_3_4) ≤ (t - 1)) ∧ ((x_4_7 - x_3_7) ≤ (t - 1))) ∨ ((x_4_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_4) ∧ ((x_3_4 - x_4_7) ≥ 1) ∧ ((x_3_4 - x_3_7) ≤ (t - 1)) ∧ ((x_3_7 - x_4_7) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_7) ∧ (x_3_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_4_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_4 ≤ x_3_7) ↔ (((1) * x_3_4 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_7 ≤ x_4_7) ↔ (((1) * x_3_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_7 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_7 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_4_7) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_4 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_7 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory107 (x_3_4 x_4_5 x_4_7 : ℝ) : (¬ ((x_3_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_3_4 + ((-1) * x_4_7)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory108 (t x_3_7 x_3_9 x_7_9 : ℝ) : ((((x_3_7 ≤ x_3_9) ∧ (x_3_9 ≤ x_7_9) ∧ ((x_7_9 - x_3_7) ≥ 1) ∧ ((x_3_9 - x_3_7) ≤ (t - 1)) ∧ ((x_7_9 - x_3_9) ≤ (t - 1))) ∨ ((x_7_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_7) ∧ ((x_3_7 - x_7_9) ≥ 1) ∧ ((x_3_7 - x_3_9) ≤ (t - 1)) ∧ ((x_3_9 - x_7_9) ≤ (t - 1)))) ↔ (((x_3_7 ≤ x_3_9) ∧ (x_3_9 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_3_9 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_3_9)) ≤ ((-1) + t))) ∨ ((x_7_9 ≤ x_3_9) ∧ (x_3_9 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_9)) ≤ ((-1) + t)) ∧ ((x_3_9 + ((-1) * x_7_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_7 + ((-1) * x_7_9)) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_7 ≤ x_3_9) ↔ (((1) * x_3_7 + (-1) * x_3_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_9 ≤ x_7_9) ↔ (((1) * x_3_9 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_3_7) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_9 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_9 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_3_9) ↔ (¬ (((1) * x_3_9 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_9 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_3_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_7 - x_7_9) ≥ 1) ↔ (¬ (((1) * x_3_7 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_7 - x_3_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_3_7)) ≥ 1) ↔ (((1) * x_3_7 + (-1) * x_7_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_9 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_9 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_9 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_7 + ((-1) * x_3_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_3_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_9 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory109 (t x_7_8 x_7_9 x_8_9 : ℝ) : ((((x_7_8 ≤ x_7_9) ∧ (x_7_9 ≤ x_8_9) ∧ ((x_8_9 - x_7_8) ≥ 1) ∧ ((x_7_9 - x_7_8) ≤ (t - 1)) ∧ ((x_8_9 - x_7_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_7_9) ∧ (x_7_9 ≤ x_7_8) ∧ ((x_7_8 - x_8_9) ≥ 1) ∧ ((x_7_8 - x_7_9) ≤ (t - 1)) ∧ ((x_7_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_7_8 ≤ x_7_9) ∧ (x_7_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_7_9 + ((-1) * x_7_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_7_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_7_9) ∧ (x_7_9 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_7_8 + ((-1) * x_7_9)) ≤ ((-1) + t)) ∧ ((x_7_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_7_8 ≤ x_7_9) ↔ (((1) * x_7_8 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_7_9 ≤ x_8_9) ↔ (((1) * x_7_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_8_9 - x_7_8) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_9 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_8 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_8_9 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_8_9 ≤ x_7_9) ↔ (¬ (((1) * x_7_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_9 ≤ x_7_8) ↔ (¬ (((1) * x_7_8 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_7_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_7_8 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_8 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_8_9 + ((-1) * x_7_8)) ≥ 1) ↔ (((1) * x_7_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_9 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_8 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_8_9 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_7_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_8 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_8 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory110 (t x_7_9 : ℝ) : ((¬ (t ≤ x_7_9)) ↔ (¬ ((t + ((-1) * x_7_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_7_9) ↔ (((1) * t + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_7_9)) ≤ 0) ↔ (((1) * t + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory111 (t x_0_4 x_0_8 x_4_8 : ℝ) : ((((x_0_4 ≤ x_0_8) ∧ (x_0_8 ≤ x_4_8) ∧ ((x_4_8 - x_0_4) ≥ 1) ∧ ((x_0_8 - x_0_4) ≤ (t - 1)) ∧ ((x_4_8 - x_0_8) ≤ (t - 1))) ∨ ((x_4_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_4) ∧ ((x_0_4 - x_4_8) ≥ 1) ∧ ((x_0_4 - x_0_8) ≤ (t - 1)) ∧ ((x_0_8 - x_4_8) ≤ (t - 1)))) ↔ (((x_0_4 ≤ x_0_8) ∧ (x_0_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_8 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_0_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_0_8) ∧ (x_0_8 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_8)) ≤ ((-1) + t)) ∧ ((x_0_8 + ((-1) * x_4_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_0_8) ↔ (((1) * x_0_4 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_8 ≤ x_4_8) ↔ (((1) * x_0_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_8 - x_0_4) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_8 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_8 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_8 ≤ x_0_8) ↔ (¬ (((1) * x_0_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_8 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_4 - x_4_8) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_0_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_8 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_8 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_8 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory112 (t x_0_4 x_0_8 x_4_8 : ℝ) : ((((x_0_4 + ((-1) * x_0_8)) ≤ 0) ∧ ((x_0_8 + ((-1) * x_4_8)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_8)) ≥ 1) ∧ ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + x_0_4 + ((-1) * x_0_8)) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≤ 0))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_0_8)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_8 + ((-1) * x_4_8)) ≤ 0) ↔ (((1) * x_0_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_4_8)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_4 + ((-1) * x_0_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_8 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory113 (t x_0_4 x_0_8 x_4_8 : ℝ) : ((((x_0_8 + ((-1) * x_4_8)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_8)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_8) ≥ 1) ∧ ((t + ((-1) * x_0_8) + x_4_8) ≥ 1)) ↔ (¬ ((¬ ((x_0_4 + ((-1) * x_4_8)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_0_8) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_8) + x_4_8) ≥ 1)) ∨ (¬ ((x_0_8 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_0_8)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_4) + x_0_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + ((-1) * x_0_8) + x_4_8) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_8 + ((-1) * x_4_8)) ≥ 0) ↔ (¬ (((1) * x_0_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_4 + ((-1) * x_0_8)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory114 (t x_1_4 x_1_6 x_4_6 : ℝ) : ((((x_1_4 ≤ x_1_6) ∧ (x_1_6 ≤ x_4_6) ∧ ((x_4_6 - x_1_4) ≥ 1) ∧ ((x_1_6 - x_1_4) ≤ (t - 1)) ∧ ((x_4_6 - x_1_6) ≤ (t - 1))) ∨ ((x_4_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_4) ∧ ((x_1_4 - x_4_6) ≥ 1) ∧ ((x_1_4 - x_1_6) ≤ (t - 1)) ∧ ((x_1_6 - x_4_6) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_6) ∧ (x_1_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_4_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_4 ≤ x_1_6) ↔ (((1) * x_1_4 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_6 ≤ x_4_6) ↔ (((1) * x_1_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_6 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_6 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_6 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_6 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_4_6) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_4 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_6 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory115 (t x_1_4 x_1_6 x_4_6 : ℝ) : ((((x_1_4 + ((-1) * x_1_6)) ≤ 0) ∧ ((x_1_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_6)) ≥ 1) ∧ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + x_1_4 + ((-1) * x_1_6)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_6)) ≤ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_1_6)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_1_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_4 + ((-1) * x_1_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory116 (t x_1_4 x_1_6 x_4_6 : ℝ) : ((((x_1_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_6)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_6) ≥ 1) ∧ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1)) ↔ (¬ ((¬ ((x_1_4 + ((-1) * x_1_6)) ≥ 0)) ∨ (¬ ((x_1_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_6) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_6) + x_4_6) ≥ 1))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_1_6)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_1_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_1_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory117 (x_1_4 x_4_6 x_4_8 : ℝ) : (¬ ((x_1_4 + ((-1) * x_4_8)) ≤ (-1))) ∨ (¬ ((x_4_6 + ((-1) * x_4_8)) ≥ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory118 (t x_1_4 x_1_8 x_4_8 : ℝ) : ((((x_1_4 ≤ x_1_8) ∧ (x_1_8 ≤ x_4_8) ∧ ((x_4_8 - x_1_4) ≥ 1) ∧ ((x_1_8 - x_1_4) ≤ (t - 1)) ∧ ((x_4_8 - x_1_8) ≤ (t - 1))) ∨ ((x_4_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_4) ∧ ((x_1_4 - x_4_8) ≥ 1) ∧ ((x_1_4 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_4_8) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_8) ∧ (x_1_8 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_4_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_4_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_4 ≤ x_1_8) ↔ (((1) * x_1_4 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_4_8) ↔ (((1) * x_1_8 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_8 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_4 - x_4_8) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_4_8)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory119 (t x_4_8 x_4_9 x_8_9 : ℝ) : ((((x_4_8 ≤ x_4_9) ∧ (x_4_9 ≤ x_8_9) ∧ ((x_8_9 - x_4_8) ≥ 1) ∧ ((x_4_9 - x_4_8) ≤ (t - 1)) ∧ ((x_8_9 - x_4_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_8) ∧ ((x_4_8 - x_8_9) ≥ 1) ∧ ((x_4_8 - x_4_9) ≤ (t - 1)) ∧ ((x_4_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_4_8 ≤ x_4_9) ∧ (x_4_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_4_8)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_8) ∧ ((x_4_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_8 ≤ x_4_9) ↔ (((1) * x_4_8 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_9 ≤ x_8_9) ↔ (((1) * x_4_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_4_8) ≥ 1) ↔ (((1) * x_4_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_4_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_8 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_4_8)) ≥ 1) ↔ (((1) * x_4_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_8 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory120 (x_4_8 x_5_8 x_5_9 x_8_9 : ℝ) : (¬ ((x_4_8 + ((-1) * x_5_8)) ≥ 0)) ∨ (¬ ((x_5_9 + ((-1) * x_8_9)) ≥ 0)) ∨ (¬ ((x_5_8 + ((-1) * x_5_9)) ≥ 0)) ∨ (¬ ((x_4_8 + ((-1) * x_8_9)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory121 (t x_3_4 x_3_5 x_4_5 : ℝ) : ((((x_3_4 ≤ x_3_5) ∧ (x_3_5 ≤ x_4_5) ∧ ((x_4_5 - x_3_4) ≥ 1) ∧ ((x_3_5 - x_3_4) ≤ (t - 1)) ∧ ((x_4_5 - x_3_5) ≤ (t - 1))) ∨ ((x_4_5 ≤ x_3_5) ∧ (x_3_5 ≤ x_3_4) ∧ ((x_3_4 - x_4_5) ≥ 1) ∧ ((x_3_4 - x_3_5) ≤ (t - 1)) ∧ ((x_3_5 - x_4_5) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_5) ∧ (x_3_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_3_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_3_5) ∧ (x_3_5 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_4_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_4 ≤ x_3_5) ↔ (((1) * x_3_4 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_5 ≤ x_4_5) ↔ (((1) * x_3_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_5 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_5 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_5 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_5 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_5 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_4 - x_4_5) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_5 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_5 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_5 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory122 (t x_3_4 : ℝ) : ((¬ (t ≤ x_3_4)) ↔ (¬ ((t + ((-1) * x_3_4)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_4) ↔ (((1) * t + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_4)) ≤ 0) ↔ (((1) * t + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory123 (t x_4_6 x_4_7 x_6_7 : ℝ) : ((((x_4_6 ≤ x_4_7) ∧ (x_4_7 ≤ x_6_7) ∧ ((x_6_7 - x_4_6) ≥ 1) ∧ ((x_4_7 - x_4_6) ≤ (t - 1)) ∧ ((x_6_7 - x_4_7) ≤ (t - 1))) ∨ ((x_6_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_6) ∧ ((x_4_6 - x_6_7) ≥ 1) ∧ ((x_4_6 - x_4_7) ≤ (t - 1)) ∧ ((x_4_7 - x_6_7) ≤ (t - 1)))) ↔ (((x_4_6 ≤ x_4_7) ∧ (x_4_7 ≤ x_6_7) ∧ ((x_6_7 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_6_7 + ((-1) * x_4_7)) ≤ ((-1) + t))) ∨ ((x_6_7 ≤ x_4_7) ∧ (x_4_7 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_6_7)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_6_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_6 + ((-1) * x_6_7)) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_6 ≤ x_4_7) ↔ (((1) * x_4_6 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_7 ≤ x_6_7) ↔ (((1) * x_4_7 + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_7 - x_4_6) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_7 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_7 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_6_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_7 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_6 - x_6_7) ≥ 1) ↔ (¬ (((1) * x_4_6 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_6 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_7 - x_6_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_7 + ((-1) * x_4_6)) ≥ 1) ↔ (((1) * x_4_6 + (-1) * x_6_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_7 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_6 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_7 + ((-1) * x_6_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_6_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory124 (t x_4_5 x_4_6 x_5_6 : ℝ) : ((((x_4_5 ≤ x_4_6) ∧ (x_4_6 ≤ x_5_6) ∧ ((x_5_6 - x_4_5) ≥ 1) ∧ ((x_4_6 - x_4_5) ≤ (t - 1)) ∧ ((x_5_6 - x_4_6) ≤ (t - 1))) ∨ ((x_5_6 ≤ x_4_6) ∧ (x_4_6 ≤ x_4_5) ∧ ((x_4_5 - x_5_6) ≥ 1) ∧ ((x_4_5 - x_4_6) ≤ (t - 1)) ∧ ((x_4_6 - x_5_6) ≤ (t - 1)))) ↔ (((x_4_5 ≤ x_4_6) ∧ (x_4_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_6 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_4_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_4_6) ∧ (x_4_6 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_6)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_5_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_5 ≤ x_4_6) ↔ (((1) * x_4_5 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_6 ≤ x_5_6) ↔ (((1) * x_4_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_6 - x_4_5) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_6 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_6 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_6 ≤ x_4_6) ↔ (¬ (((1) * x_4_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_6 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 - x_5_6) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_6 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_6 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_6 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory125 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((((x_0_4 ≤ x_0_6) ∧ (x_0_6 ≤ x_4_6) ∧ ((x_4_6 - x_0_4) ≥ 1) ∧ ((x_0_6 - x_0_4) ≤ (t - 1)) ∧ ((x_4_6 - x_0_6) ≤ (t - 1))) ∨ ((x_4_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_4) ∧ ((x_0_4 - x_4_6) ≥ 1) ∧ ((x_0_4 - x_0_6) ≤ (t - 1)) ∧ ((x_0_6 - x_4_6) ≤ (t - 1)))) ↔ (((x_0_4 ≤ x_0_6) ∧ (x_0_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_0_4)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_4) ∧ ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_4_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_0_6) ↔ (((1) * x_0_4 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_6 ≤ x_4_6) ↔ (((1) * x_0_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_6 - x_0_4) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_6 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_4 - x_4_6) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_6 + ((-1) * x_0_4)) ≥ 1) ↔ (((1) * x_0_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_4 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory126 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((((x_0_4 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_4_6)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) ∧ ((t + x_0_4 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≤ (-1))) ∨ (¬ ((t + x_0_4 + ((-1) * x_0_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_6 + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_4_6)) ≤ (-1)) ↔ (((1) * x_0_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_0_4 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_0_6 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory127 (t x_0_4 x_0_6 x_4_6 : ℝ) : ((((x_0_6 + ((-1) * x_4_6)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ↔ (¬ ((¬ ((x_0_4 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_6) + x_4_6) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_4) + x_0_6) ≥ 1))))) := by
  classical
  have e0 : ((x_0_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_0_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_6 + ((-1) * x_4_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_6) + x_4_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_4) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory128 (x_0_6 x_0_7 x_4_6 x_6_7 : ℝ) : (¬ ((x_0_7 + ((-1) * x_6_7)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_0_7)) ≥ 0)) ∨ (¬ ((x_4_6 + ((-1) * x_6_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory129 (x_0_4 x_4_5 x_4_6 : ℝ) : (¬ ((x_0_4 + ((-1) * x_4_5)) ≤ (-1))) ∨ (¬ ((x_4_5 + ((-1) * x_4_6)) ≤ 0)) ∨ (¬ ((x_0_4 + ((-1) * x_4_6)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory130 (t x_0_2 x_0_4 x_2_4 : ℝ) : ((((x_0_2 ≤ x_0_4) ∧ (x_0_4 ≤ x_2_4) ∧ ((x_2_4 - x_0_2) ≥ 1) ∧ ((x_0_4 - x_0_2) ≤ (t - 1)) ∧ ((x_2_4 - x_0_4) ≤ (t - 1))) ∨ ((x_2_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_2) ∧ ((x_0_2 - x_2_4) ≥ 1) ∧ ((x_0_2 - x_0_4) ≤ (t - 1)) ∧ ((x_0_4 - x_2_4) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_4) ∧ (x_0_4 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_2_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_2_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_2 ≤ x_0_4) ↔ (((1) * x_0_2 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_2_4) ↔ (((1) * x_0_4 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_4 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_4 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_4 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_4 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 - x_2_4) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_4 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_4 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_2_4)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory131 (t x_0_1 x_0_2 x_1_2 : ℝ) : ((((x_0_1 ≤ x_0_2) ∧ (x_0_2 ≤ x_1_2) ∧ ((x_1_2 - x_0_1) ≥ 1) ∧ ((x_0_2 - x_0_1) ≤ (t - 1)) ∧ ((x_1_2 - x_0_2) ≤ (t - 1))) ∨ ((x_1_2 ≤ x_0_2) ∧ (x_0_2 ≤ x_0_1) ∧ ((x_0_1 - x_1_2) ≥ 1) ∧ ((x_0_1 - x_0_2) ≤ (t - 1)) ∧ ((x_0_2 - x_1_2) ≤ (t - 1)))) ↔ (((x_0_1 ≤ x_0_2) ∧ (x_0_2 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_0_1)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_1)) ≤ ((-1) + t)) ∧ ((x_1_2 + ((-1) * x_0_2)) ≤ ((-1) + t))) ∨ ((x_1_2 ≤ x_0_2) ∧ (x_0_2 ≤ x_0_1) ∧ ((x_0_1 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_0_1 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_0_2 + ((-1) * x_1_2)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_1 + ((-1) * x_1_2)) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_1 ≤ x_0_2) ↔ (((1) * x_0_1 + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_2 ≤ x_1_2) ↔ (((1) * x_0_2 + (-1) * x_1_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_2 - x_0_1) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_2 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_2 - x_0_1) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_1_2 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_2 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_1_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_2 ≤ x_0_1) ↔ (¬ (((1) * x_0_1 + (-1) * x_0_2) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_1 - x_1_2) ≥ 1) ↔ (¬ (((1) * x_0_1 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_1 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_2 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_2 + ((-1) * x_0_1)) ≥ 1) ↔ (((1) * x_0_1 + (-1) * x_1_2 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_2 + ((-1) * x_0_1)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_1 + (-1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_1 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_1 + (1) * x_0_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_2 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_1_2 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory132 (t x_0_2 : ℝ) : ((¬ (t ≤ x_0_2)) ↔ (¬ ((t + ((-1) * x_0_2)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_2) ↔ (((1) * t + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_2)) ≤ 0) ↔ (((1) * t + (-1) * x_0_2) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory133 (t x_2_5 x_2_8 x_5_8 : ℝ) : ((((x_2_5 ≤ x_2_8) ∧ (x_2_8 ≤ x_5_8) ∧ ((x_5_8 - x_2_5) ≥ 1) ∧ ((x_2_8 - x_2_5) ≤ (t - 1)) ∧ ((x_5_8 - x_2_8) ≤ (t - 1))) ∨ ((x_5_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_5) ∧ ((x_2_5 - x_5_8) ≥ 1) ∧ ((x_2_5 - x_2_8) ≤ (t - 1)) ∧ ((x_2_8 - x_5_8) ≤ (t - 1)))) ↔ (((x_2_5 ≤ x_2_8) ∧ (x_2_8 ≤ x_5_8) ∧ ((x_5_8 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_5_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_8)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_5_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_8)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_5 ≤ x_2_8) ↔ (((1) * x_2_5 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_8 ≤ x_5_8) ↔ (((1) * x_2_8 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_8 - x_2_5) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_8 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_8 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_5 - x_5_8) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_5 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_8 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_8 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory134 (t x_2_3 : ℝ) : ((¬ (t ≤ x_2_3)) ↔ (¬ ((t + ((-1) * x_2_3)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_3) ↔ (((1) * t + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_3)) ≤ 0) ↔ (((1) * t + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory135 (t x_2_3 x_2_4 x_3_4 : ℝ) : ((((x_2_3 ≤ x_2_4) ∧ (x_2_4 ≤ x_3_4) ∧ ((x_3_4 - x_2_3) ≥ 1) ∧ ((x_2_4 - x_2_3) ≤ (t - 1)) ∧ ((x_3_4 - x_2_4) ≤ (t - 1))) ∨ ((x_3_4 ≤ x_2_4) ∧ (x_2_4 ≤ x_2_3) ∧ ((x_2_3 - x_3_4) ≥ 1) ∧ ((x_2_3 - x_2_4) ≤ (t - 1)) ∧ ((x_2_4 - x_3_4) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_4) ∧ (x_2_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_2_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_2_4) ∧ (x_2_4 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_2_4 + ((-1) * x_3_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_3 ≤ x_2_4) ↔ (((1) * x_2_3 + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_4 ≤ x_3_4) ↔ (((1) * x_2_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_4 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_4 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_4 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_4 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_4 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_3_4) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_4 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_4 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_4 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory136 (t x_7_8 : ℝ) : ((¬ (t ≤ x_7_8)) ↔ (¬ ((t + ((-1) * x_7_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_7_8) ↔ (((1) * t + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_7_8)) ≤ 0) ↔ (((1) * t + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory137 (t x_1_3 x_1_6 x_3_6 : ℝ) : ((((x_1_3 ≤ x_1_6) ∧ (x_1_6 ≤ x_3_6) ∧ ((x_3_6 - x_1_3) ≥ 1) ∧ ((x_1_6 - x_1_3) ≤ (t - 1)) ∧ ((x_3_6 - x_1_6) ≤ (t - 1))) ∨ ((x_3_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_3) ∧ ((x_1_3 - x_3_6) ≥ 1) ∧ ((x_1_3 - x_1_6) ≤ (t - 1)) ∧ ((x_1_6 - x_3_6) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_6) ∧ (x_1_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_3_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_3 ≤ x_1_6) ↔ (((1) * x_1_3 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_6 ≤ x_3_6) ↔ (((1) * x_1_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_6 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_6 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_6 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_6 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_3 - x_3_6) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_6 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_6 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_6 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory138 (t x_0_3 x_0_4 x_3_4 : ℝ) : ((((x_0_3 ≤ x_0_4) ∧ (x_0_4 ≤ x_3_4) ∧ ((x_3_4 - x_0_3) ≥ 1) ∧ ((x_0_4 - x_0_3) ≤ (t - 1)) ∧ ((x_3_4 - x_0_4) ≤ (t - 1))) ∨ ((x_3_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_3) ∧ ((x_0_3 - x_3_4) ≥ 1) ∧ ((x_0_3 - x_0_4) ≤ (t - 1)) ∧ ((x_0_4 - x_3_4) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_4) ∧ (x_0_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_4 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_0_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_0_4) ∧ (x_0_4 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_4)) ≤ ((-1) + t)) ∧ ((x_0_4 + ((-1) * x_3_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_3 ≤ x_0_4) ↔ (((1) * x_0_3 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_4 ≤ x_3_4) ↔ (((1) * x_0_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_4 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_4 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_0_4) ↔ (¬ (((1) * x_0_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_4 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_3 - x_3_4) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_0_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_4 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_4 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_4 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory139 (t x_0_3 x_0_4 x_3_4 : ℝ) : ((((x_0_3 + ((-1) * x_0_4)) ≤ 0) ∧ ((x_0_4 + ((-1) * x_3_4)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_4)) ≥ 1) ∧ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((t + x_0_3 + ((-1) * x_0_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_4)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)))))) := by
  classical
  have e0 : ((t + x_0_4 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_3 + ((-1) * x_0_4)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_4 + ((-1) * x_3_4)) ≤ 0) ↔ (((1) * x_0_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 + ((-1) * x_0_4)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_3 + ((-1) * x_3_4)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory140 (t x_0_3 x_0_4 x_3_4 : ℝ) : ((((x_0_4 + ((-1) * x_3_4)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_4)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_4) ≥ 1) ∧ ((t + ((-1) * x_0_4) + x_3_4) ≥ 1)) ↔ (¬ ((¬ ((x_0_3 + ((-1) * x_0_4)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) ∨ (¬ ((x_0_4 + ((-1) * x_3_4)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_4) + x_3_4) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_4) ≥ 1))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_4 + ((-1) * x_3_4)) ≥ 0) ↔ (¬ (((1) * x_0_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_3 + ((-1) * x_0_4)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_3) + x_0_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_4) + x_3_4) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory141 (x_0_6 x_3_6 x_6_8 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_6_8)) ≤ (-1))) ∨ (¬ ((x_3_6 + ((-1) * x_6_8)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory142 (t x_3_6 x_3_8 x_6_8 : ℝ) : ((((x_3_6 ≤ x_3_8) ∧ (x_3_8 ≤ x_6_8) ∧ ((x_6_8 - x_3_6) ≥ 1) ∧ ((x_3_8 - x_3_6) ≤ (t - 1)) ∧ ((x_6_8 - x_3_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_6) ∧ ((x_3_6 - x_6_8) ≥ 1) ∧ ((x_3_6 - x_3_8) ≤ (t - 1)) ∧ ((x_3_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_3_6 ≤ x_3_8) ∧ (x_3_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_3_8 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_3_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_3_8) ∧ (x_3_8 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_8)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_3_8) ↔ (((1) * x_3_6 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_8 ≤ x_6_8) ↔ (((1) * x_3_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_6_8 - x_3_6) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_8 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_6_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_6_8 ≤ x_3_8) ↔ (¬ (((1) * x_3_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_8 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_3_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_6_8 + ((-1) * x_3_6)) ≥ 1) ↔ (((1) * x_3_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_6_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_6 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory143 (t x_2_3 x_2_7 x_3_7 : ℝ) : ((((x_2_3 ≤ x_2_7) ∧ (x_2_7 ≤ x_3_7) ∧ ((x_3_7 - x_2_3) ≥ 1) ∧ ((x_2_7 - x_2_3) ≤ (t - 1)) ∧ ((x_3_7 - x_2_7) ≤ (t - 1))) ∨ ((x_3_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_3) ∧ ((x_2_3 - x_3_7) ≥ 1) ∧ ((x_2_3 - x_2_7) ≤ (t - 1)) ∧ ((x_2_7 - x_3_7) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_7) ∧ (x_2_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_3_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_3 ≤ x_2_7) ↔ (((1) * x_2_3 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_7 ≤ x_3_7) ↔ (((1) * x_2_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_7 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_7 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_7 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_3 - x_3_7) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_7 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory144 (t x_1_3 : ℝ) : ((¬ (t ≤ x_1_3)) ↔ (¬ ((t + ((-1) * x_1_3)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_3) ↔ (((1) * t + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_3)) ≤ 0) ↔ (((1) * t + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory145 (t x_0_2 x_0_3 x_2_3 : ℝ) : ((((x_0_2 ≤ x_0_3) ∧ (x_0_3 ≤ x_2_3) ∧ ((x_2_3 - x_0_2) ≥ 1) ∧ ((x_0_3 - x_0_2) ≤ (t - 1)) ∧ ((x_2_3 - x_0_3) ≤ (t - 1))) ∨ ((x_2_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_2) ∧ ((x_0_2 - x_2_3) ≥ 1) ∧ ((x_0_2 - x_0_3) ≤ (t - 1)) ∧ ((x_0_3 - x_2_3) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_3) ∧ (x_0_3 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_3 + ((-1) * x_0_3)) ≤ ((-1) + t))) ∨ ((x_2_3 ≤ x_0_3) ∧ (x_0_3 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_0_3 + ((-1) * x_2_3)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_2 ≤ x_0_3) ↔ (((1) * x_0_2 + (-1) * x_0_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_3 ≤ x_2_3) ↔ (((1) * x_0_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_3 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_3 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_3 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_3 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_2 - x_2_3) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_3 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_3 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_3 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_3 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_2 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_3 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory146 (t x_0_1 : ℝ) : ((¬ (t ≤ x_0_1)) ↔ (¬ ((t + ((-1) * x_0_1)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_0_1) ↔ (((1) * t + (-1) * x_0_1) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_0_1)) ≤ 0) ↔ (((1) * t + (-1) * x_0_1) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory147 (t x_1_2 x_1_7 x_2_7 : ℝ) : ((((x_1_2 ≤ x_1_7) ∧ (x_1_7 ≤ x_2_7) ∧ ((x_2_7 - x_1_2) ≥ 1) ∧ ((x_1_7 - x_1_2) ≤ (t - 1)) ∧ ((x_2_7 - x_1_7) ≤ (t - 1))) ∨ ((x_2_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_2) ∧ ((x_1_2 - x_2_7) ≥ 1) ∧ ((x_1_2 - x_1_7) ≤ (t - 1)) ∧ ((x_1_7 - x_2_7) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_7) ∧ (x_1_7 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_2_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_2_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_2 ≤ x_1_7) ↔ (((1) * x_1_2 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_2_7) ↔ (((1) * x_1_7 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_7 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_7 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 - x_2_7) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_7 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_2_7)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory148 (t x_2_7 x_2_8 x_7_8 : ℝ) : ((((x_2_7 ≤ x_2_8) ∧ (x_2_8 ≤ x_7_8) ∧ ((x_7_8 - x_2_7) ≥ 1) ∧ ((x_2_8 - x_2_7) ≤ (t - 1)) ∧ ((x_7_8 - x_2_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_7) ∧ ((x_2_7 - x_7_8) ≥ 1) ∧ ((x_2_7 - x_2_8) ≤ (t - 1)) ∧ ((x_2_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_2_7 ≤ x_2_8) ∧ (x_2_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_2_7)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_7) ∧ ((x_2_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_7 ≤ x_2_8) ↔ (((1) * x_2_7 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_8 ≤ x_7_8) ↔ (((1) * x_2_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 - x_2_7) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_8 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_8 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_2_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_7 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_2_7)) ≥ 1) ↔ (((1) * x_2_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_8 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_7 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory149 (t x_1_3 x_1_4 x_3_4 : ℝ) : ((((x_1_3 ≤ x_1_4) ∧ (x_1_4 ≤ x_3_4) ∧ ((x_3_4 - x_1_3) ≥ 1) ∧ ((x_1_4 - x_1_3) ≤ (t - 1)) ∧ ((x_3_4 - x_1_4) ≤ (t - 1))) ∨ ((x_3_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_3) ∧ ((x_1_3 - x_3_4) ≥ 1) ∧ ((x_1_3 - x_1_4) ≤ (t - 1)) ∧ ((x_1_4 - x_3_4) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_4) ∧ (x_1_4 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_4 + ((-1) * x_1_4)) ≤ ((-1) + t))) ∨ ((x_3_4 ≤ x_1_4) ∧ (x_1_4 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_1_4 + ((-1) * x_3_4)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_3 ≤ x_1_4) ↔ (((1) * x_1_3 + (-1) * x_1_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_4 ≤ x_3_4) ↔ (((1) * x_1_4 + (-1) * x_3_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_4 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_4 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_4 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_4 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_3_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_4 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_4) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_3 - x_3_4) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_4 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_4 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_4 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_4 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_4 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_3_4)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_4 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_3_4 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory150 (t x_1_2 x_1_3 x_2_3 : ℝ) : ((((x_1_2 ≤ x_1_3) ∧ (x_1_3 ≤ x_2_3) ∧ ((x_2_3 - x_1_2) ≥ 1) ∧ ((x_1_3 - x_1_2) ≤ (t - 1)) ∧ ((x_2_3 - x_1_3) ≤ (t - 1))) ∨ ((x_2_3 ≤ x_1_3) ∧ (x_1_3 ≤ x_1_2) ∧ ((x_1_2 - x_2_3) ≥ 1) ∧ ((x_1_2 - x_1_3) ≤ (t - 1)) ∧ ((x_1_3 - x_2_3) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_3) ∧ (x_1_3 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_3 + ((-1) * x_1_3)) ≤ ((-1) + t))) ∨ ((x_2_3 ≤ x_1_3) ∧ (x_1_3 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_1_3 + ((-1) * x_2_3)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_2 ≤ x_1_3) ↔ (((1) * x_1_2 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_3 ≤ x_2_3) ↔ (((1) * x_1_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_3 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_3 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_3 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_3 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_3 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_2_3) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_2 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_3 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_3 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_3 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_3 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_3 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory151 (t x_1_2 x_1_3 x_2_3 : ℝ) : ((((x_1_2 + ((-1) * x_1_3)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_2_3)) ≤ 0) ∧ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1)) ∧ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1) ∧ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1)) ∨ (¬ ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≤ 0))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_1_3)) ≤ 0) ↔ (((1) * x_1_2 + (-1) * x_1_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_3 + ((-1) * x_2_3)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_2_3) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_2 + ((-1) * x_2_3)) ≤ (-1)) ↔ (((1) * x_1_2 + (-1) * x_2_3 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_2 + ((-1) * x_1_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_3 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory152 (t x_1_2 x_1_3 x_2_3 : ℝ) : ((((x_1_3 + ((-1) * x_2_3)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_1_3)) ≥ 0) ∧ ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ∧ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1)) ↔ (¬ ((¬ ((x_1_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_2) + x_1_3) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_2_3)) ≥ 0)) ∨ (¬ ((x_1_2 + ((-1) * x_1_3)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_3) + x_2_3) ≥ 1))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_3)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_2) + x_1_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_2_3)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_2_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_2 + ((-1) * x_1_3)) ≥ 0) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_3) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_3) + x_2_3) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_2_3 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory153 (x_0_2 x_1_2 x_2_3 : ℝ) : (¬ ((x_0_2 + ((-1) * x_1_2)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_3)) ≥ 1)) ∨ (¬ ((x_1_2 + ((-1) * x_2_3)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory154 (t x_7_10 x_7_9 x_9_10 : ℝ) : ((((x_7_9 ≤ x_7_10) ∧ (x_7_10 ≤ x_9_10) ∧ ((x_9_10 - x_7_9) ≥ 1) ∧ ((x_7_10 - x_7_9) ≤ (t - 1)) ∧ ((x_9_10 - x_7_10) ≤ (t - 1))) ∨ ((x_9_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_9) ∧ ((x_7_9 - x_9_10) ≥ 1) ∧ ((x_7_9 - x_7_10) ≤ (t - 1)) ∧ ((x_7_10 - x_9_10) ≤ (t - 1)))) ↔ (((x_7_9 ≤ x_7_10) ∧ (x_7_10 ≤ x_9_10) ∧ ((x_9_10 + ((-1) * x_7_9)) ≥ 1) ∧ ((x_7_10 + ((-1) * x_7_9)) ≤ ((-1) + t)) ∧ ((x_9_10 + ((-1) * x_7_10)) ≤ ((-1) + t))) ∨ ((x_9_10 ≤ x_7_10) ∧ (x_7_10 ≤ x_7_9) ∧ ((x_7_9 + ((-1) * x_9_10)) ≥ 1) ∧ ((x_7_9 + ((-1) * x_7_10)) ≤ ((-1) + t)) ∧ ((x_7_10 + ((-1) * x_9_10)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_7_9 + ((-1) * x_9_10)) ≥ 1) ↔ (¬ (((1) * x_7_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_7_9 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_7_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_7_10 ≤ x_9_10) ↔ (((1) * x_7_10 + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_9_10 - x_7_9) ≥ 1) ↔ (((1) * x_7_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_7_10 - x_7_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_9_10 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_9_10 ≤ x_7_10) ↔ (¬ (((1) * x_7_10 + (-1) * x_9_10) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_7_10 ≤ x_7_9) ↔ (((1) * x_7_10 + (-1) * x_7_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_7_9 - x_9_10) ≥ 1) ↔ (¬ (((1) * x_7_9 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_7_9 - x_7_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_7_10 - x_9_10) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_9_10 + ((-1) * x_7_9)) ≥ 1) ↔ (((1) * x_7_9 + (-1) * x_9_10 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_7_10 + ((-1) * x_7_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_9_10 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_7_9 + ((-1) * x_7_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_7_10 + (-1) * x_7_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_7_10 + ((-1) * x_9_10)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_7_10 + (1) * x_9_10 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory155 (t x_9_10 : ℝ) : ((¬ (t ≤ x_9_10)) ↔ (¬ ((t + ((-1) * x_9_10)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_9_10) ↔ (((1) * t + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_9_10)) ≤ 0) ↔ (((1) * t + (-1) * x_9_10) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory156 (t x_5_6 : ℝ) : ((¬ (t ≤ x_5_6)) ↔ (¬ ((t + ((-1) * x_5_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_5_6) ↔ (((1) * t + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_5_6)) ≤ 0) ↔ (((1) * t + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory157 (t x_8_9 : ℝ) : ((¬ (t ≤ x_8_9)) ↔ (¬ ((t + ((-1) * x_8_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_8_9) ↔ (((1) * t + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_8_9)) ≤ 0) ↔ (((1) * t + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory158 (t x_0_2 x_0_6 x_2_6 : ℝ) : ((((x_0_2 ≤ x_0_6) ∧ (x_0_6 ≤ x_2_6) ∧ ((x_2_6 - x_0_2) ≥ 1) ∧ ((x_0_6 - x_0_2) ≤ (t - 1)) ∧ ((x_2_6 - x_0_6) ≤ (t - 1))) ∨ ((x_2_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_2) ∧ ((x_0_2 - x_2_6) ≥ 1) ∧ ((x_0_2 - x_0_6) ≤ (t - 1)) ∧ ((x_0_6 - x_2_6) ≤ (t - 1)))) ↔ (((x_0_2 ≤ x_0_6) ∧ (x_0_6 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_0_2)) ≥ 1) ∧ ((x_0_6 + ((-1) * x_0_2)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_0_6)) ≤ ((-1) + t))) ∨ ((x_2_6 ≤ x_0_6) ∧ (x_0_6 ≤ x_0_2) ∧ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_0_2 + ((-1) * x_0_6)) ≤ ((-1) + t)) ∧ ((x_0_6 + ((-1) * x_2_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_2 ≤ x_0_6) ↔ (((1) * x_0_2 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_6 ≤ x_2_6) ↔ (((1) * x_0_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_6 - x_0_2) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 - x_0_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_6 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_0_6) ↔ (¬ (((1) * x_0_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_6 ≤ x_0_2) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_2 - x_2_6) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_2 - x_0_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_6 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_6 + ((-1) * x_0_2)) ≥ 1) ↔ (((1) * x_0_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_6 + ((-1) * x_0_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_6 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_2 + ((-1) * x_0_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory159 (t x_0_2 x_0_6 x_2_6 : ℝ) : ((((x_0_2 + ((-1) * x_0_6)) ≤ 0) ∧ ((x_0_6 + ((-1) * x_2_6)) ≤ 0) ∧ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1)) ∧ ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1) ∧ ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≤ (-1))) ∨ (¬ ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_2 + ((-1) * x_0_6)) ≤ 0)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≤ 0))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_6)) ≤ (-1)) ↔ (((1) * x_0_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_2 + ((-1) * x_0_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_2 + (-1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_6 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_2 + ((-1) * x_0_6)) ≤ 0) ↔ (((1) * x_0_2 + (-1) * x_0_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_6 + ((-1) * x_2_6)) ≤ 0) ↔ (((1) * x_0_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory160 (t x_0_2 x_0_6 x_2_6 : ℝ) : ((((x_0_6 + ((-1) * x_2_6)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_0_6)) ≥ 0) ∧ ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((t + ((-1) * x_0_2) + x_0_6) ≥ 1) ∧ ((t + ((-1) * x_0_6) + x_2_6) ≥ 1)) ↔ (¬ ((¬ ((x_0_2 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_6)) ≥ 1)) ∨ (¬ ((x_0_6 + ((-1) * x_2_6)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_0_2) + x_0_6) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_6) + x_2_6) ≥ 1))))) := by
  classical
  have e0 : ((x_0_2 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * x_0_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_6 + ((-1) * x_2_6)) ≥ 0) ↔ (¬ (((1) * x_0_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_2 + ((-1) * x_0_6)) ≥ 0) ↔ (¬ (((1) * x_0_2 + (-1) * x_0_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_2) + x_0_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_2 + (1) * x_0_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_6) + x_2_6) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory161 (t x_2_3 x_2_6 x_3_6 : ℝ) : ((((x_2_3 ≤ x_2_6) ∧ (x_2_6 ≤ x_3_6) ∧ ((x_3_6 - x_2_3) ≥ 1) ∧ ((x_2_6 - x_2_3) ≤ (t - 1)) ∧ ((x_3_6 - x_2_6) ≤ (t - 1))) ∨ ((x_3_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_3) ∧ ((x_2_3 - x_3_6) ≥ 1) ∧ ((x_2_3 - x_2_6) ≤ (t - 1)) ∧ ((x_2_6 - x_3_6) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_6) ∧ (x_2_6 ≤ x_3_6) ∧ ((x_3_6 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_3_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_6)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_3_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_3 + ((-1) * x_3_6)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_3 ≤ x_2_6) ↔ (((1) * x_2_3 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_6 ≤ x_3_6) ↔ (((1) * x_2_6 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_6 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_6 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_6 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_6 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_3_6) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_3 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_6 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_6 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory162 (t x_0_3 x_0_7 x_3_7 : ℝ) : ((((x_0_3 ≤ x_0_7) ∧ (x_0_7 ≤ x_3_7) ∧ ((x_3_7 - x_0_3) ≥ 1) ∧ ((x_0_7 - x_0_3) ≤ (t - 1)) ∧ ((x_3_7 - x_0_7) ≤ (t - 1))) ∨ ((x_3_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_3) ∧ ((x_0_3 - x_3_7) ≥ 1) ∧ ((x_0_3 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_3_7) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_7) ∧ (x_0_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_3_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_3 ≤ x_0_7) ↔ (((1) * x_0_3 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_7 ≤ x_3_7) ↔ (((1) * x_0_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_7 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_3_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_7 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_3_7) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_3 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_7 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory163 (x_0_3 x_2_3 x_3_4 : ℝ) : (¬ ((x_2_3 + ((-1) * x_3_4)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_2_3)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory164 (t x_2_6 x_2_8 x_6_8 : ℝ) : ((((x_2_6 ≤ x_2_8) ∧ (x_2_8 ≤ x_6_8) ∧ ((x_6_8 - x_2_6) ≥ 1) ∧ ((x_2_8 - x_2_6) ≤ (t - 1)) ∧ ((x_6_8 - x_2_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_6) ∧ ((x_2_6 - x_6_8) ≥ 1) ∧ ((x_2_6 - x_2_8) ≤ (t - 1)) ∧ ((x_2_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_2_6 ≤ x_2_8) ∧ (x_2_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_6 ≤ x_2_8) ↔ (((1) * x_2_6 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_8 ≤ x_6_8) ↔ (((1) * x_2_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_8 - x_2_6) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_8 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_6 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 + ((-1) * x_2_6)) ≥ 1) ↔ (((1) * x_2_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_2_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_6 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory165 (t x_1_2 x_1_6 x_2_6 : ℝ) : ((((x_1_2 ≤ x_1_6) ∧ (x_1_6 ≤ x_2_6) ∧ ((x_2_6 - x_1_2) ≥ 1) ∧ ((x_1_6 - x_1_2) ≤ (t - 1)) ∧ ((x_2_6 - x_1_6) ≤ (t - 1))) ∨ ((x_2_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_2) ∧ ((x_1_2 - x_2_6) ≥ 1) ∧ ((x_1_2 - x_1_6) ≤ (t - 1)) ∧ ((x_1_6 - x_2_6) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_6) ∧ (x_1_6 ≤ x_2_6) ∧ ((x_2_6 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_1_6)) ≤ ((-1) + t))) ∨ ((x_2_6 ≤ x_1_6) ∧ (x_1_6 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_6)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_1_6 + ((-1) * x_2_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_2 + ((-1) * x_2_6)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_2 ≤ x_1_6) ↔ (((1) * x_1_2 + (-1) * x_1_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_6 ≤ x_2_6) ↔ (((1) * x_1_6 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_6 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_6 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_2_6 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_6 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_2_6) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_2 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_6 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_6 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_6 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_6 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory166 (t x_1_2 x_1_5 x_2_5 : ℝ) : ((((x_1_2 ≤ x_1_5) ∧ (x_1_5 ≤ x_2_5) ∧ ((x_2_5 - x_1_2) ≥ 1) ∧ ((x_1_5 - x_1_2) ≤ (t - 1)) ∧ ((x_2_5 - x_1_5) ≤ (t - 1))) ∨ ((x_2_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_2) ∧ ((x_1_2 - x_2_5) ≥ 1) ∧ ((x_1_2 - x_1_5) ≤ (t - 1)) ∧ ((x_1_5 - x_2_5) ≤ (t - 1)))) ↔ (((x_1_2 ≤ x_1_5) ∧ (x_1_5 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_1_2)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_2)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_2_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_2) ∧ ((x_1_2 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_1_2 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_2_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_2 ≤ x_1_5) ↔ (((1) * x_1_2 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_2_5) ↔ (((1) * x_1_5 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_2_5 - x_1_2) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_5 - x_1_2) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_5 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_2_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_5 ≤ x_1_2) ↔ (¬ (((1) * x_1_2 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_2 - x_2_5) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_2 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_5 + ((-1) * x_1_2)) ≥ 1) ↔ (((1) * x_1_2 + (-1) * x_2_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_5 + ((-1) * x_1_2)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_2 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_2 + ((-1) * x_2_5)) ≥ 1) ↔ (¬ (((1) * x_1_2 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_2 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_2 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory167 (t x_2_4 : ℝ) : ((¬ (t ≤ x_2_4)) ↔ (¬ ((t + ((-1) * x_2_4)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_2_4) ↔ (((1) * t + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_2_4)) ≤ 0) ↔ (((1) * t + (-1) * x_2_4) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory168 (t x_2_4 x_2_5 x_4_5 : ℝ) : ((((x_2_4 ≤ x_2_5) ∧ (x_2_5 ≤ x_4_5) ∧ ((x_4_5 - x_2_4) ≥ 1) ∧ ((x_2_5 - x_2_4) ≤ (t - 1)) ∧ ((x_4_5 - x_2_5) ≤ (t - 1))) ∨ ((x_4_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_4) ∧ ((x_2_4 - x_4_5) ≥ 1) ∧ ((x_2_4 - x_2_5) ≤ (t - 1)) ∧ ((x_2_5 - x_4_5) ≤ (t - 1)))) ↔ (((x_2_4 ≤ x_2_5) ∧ (x_2_5 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_2_4)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_4)) ≤ ((-1) + t)) ∧ ((x_4_5 + ((-1) * x_2_5)) ≤ ((-1) + t))) ∨ ((x_4_5 ≤ x_2_5) ∧ (x_2_5 ≤ x_2_4) ∧ ((x_2_4 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_2_4 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_2_5 + ((-1) * x_4_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_4 + ((-1) * x_4_5)) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_4 ≤ x_2_5) ↔ (((1) * x_2_4 + (-1) * x_2_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_5 ≤ x_4_5) ↔ (((1) * x_2_5 + (-1) * x_4_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_4_5 - x_2_4) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_5 - x_2_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_4_5 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_4_5 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_4_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_5 ≤ x_2_4) ↔ (¬ (((1) * x_2_4 + (-1) * x_2_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_4 - x_4_5) ≥ 1) ↔ (¬ (((1) * x_2_4 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_4 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_5 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_4_5 + ((-1) * x_2_4)) ≥ 1) ↔ (((1) * x_2_4 + (-1) * x_4_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_5 + ((-1) * x_2_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_4 + (-1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_4_5 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_4 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_4 + (1) * x_2_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_5 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_4_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory169 (t x_2_5 x_2_6 x_5_6 : ℝ) : ((((x_2_5 ≤ x_2_6) ∧ (x_2_6 ≤ x_5_6) ∧ ((x_5_6 - x_2_5) ≥ 1) ∧ ((x_2_6 - x_2_5) ≤ (t - 1)) ∧ ((x_5_6 - x_2_6) ≤ (t - 1))) ∨ ((x_5_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_5) ∧ ((x_2_5 - x_5_6) ≥ 1) ∧ ((x_2_5 - x_2_6) ≤ (t - 1)) ∧ ((x_2_6 - x_5_6) ≤ (t - 1)))) ↔ (((x_2_5 ≤ x_2_6) ∧ (x_2_6 ≤ x_5_6) ∧ ((x_5_6 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_6 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_6 + ((-1) * x_2_6)) ≤ ((-1) + t))) ∨ ((x_5_6 ≤ x_2_6) ∧ (x_2_6 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_6)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_6)) ≤ ((-1) + t)) ∧ ((x_2_6 + ((-1) * x_5_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_5 ≤ x_2_6) ↔ (((1) * x_2_5 + (-1) * x_2_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_6 ≤ x_5_6) ↔ (((1) * x_2_6 + (-1) * x_5_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_5_6 - x_2_5) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_6 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_6 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_5_6 ≤ x_2_6) ↔ (¬ (((1) * x_2_6 + (-1) * x_5_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_6 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_5 - x_5_6) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_5 - x_2_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_6 - x_5_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_6 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_6 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_6 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_6 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_5 + ((-1) * x_5_6)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_6 + ((-1) * x_5_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_6 + (1) * x_5_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory170 (t x_2_5 x_2_7 x_5_7 : ℝ) : ((((x_2_5 ≤ x_2_7) ∧ (x_2_7 ≤ x_5_7) ∧ ((x_5_7 - x_2_5) ≥ 1) ∧ ((x_2_7 - x_2_5) ≤ (t - 1)) ∧ ((x_5_7 - x_2_7) ≤ (t - 1))) ∨ ((x_5_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_5) ∧ ((x_2_5 - x_5_7) ≥ 1) ∧ ((x_2_5 - x_2_7) ≤ (t - 1)) ∧ ((x_2_7 - x_5_7) ≤ (t - 1)))) ↔ (((x_2_5 ≤ x_2_7) ∧ (x_2_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_2_5)) ≥ 1) ∧ ((x_2_7 + ((-1) * x_2_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_2_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_2_7) ∧ (x_2_7 ≤ x_2_5) ∧ ((x_2_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_2_5 + ((-1) * x_2_7)) ≤ ((-1) + t)) ∧ ((x_2_7 + ((-1) * x_5_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_2_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_5 ≤ x_2_7) ↔ (((1) * x_2_5 + (-1) * x_2_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_2_7 ≤ x_5_7) ↔ (((1) * x_2_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_7 - x_2_5) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_2_7 - x_2_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_7 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_2_7) ↔ (¬ (((1) * x_2_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_2_7 ≤ x_2_5) ↔ (¬ (((1) * x_2_5 + (-1) * x_2_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_5 - x_5_7) ≥ 1) ↔ (¬ (((1) * x_2_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_5 - x_2_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_2_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_2_5)) ≥ 1) ↔ (((1) * x_2_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_2_7 + ((-1) * x_2_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_5 + (-1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_5 + ((-1) * x_2_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_5 + (1) * x_2_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory171 (t x_1_5 : ℝ) : ((¬ (t ≤ x_1_5)) ↔ (¬ ((t + ((-1) * x_1_5)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_1_5) ↔ (((1) * t + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_1_5)) ≤ 0) ↔ (((1) * t + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory172 (t x_5_7 x_5_8 x_7_8 : ℝ) : ((((x_5_7 ≤ x_5_8) ∧ (x_5_8 ≤ x_7_8) ∧ ((x_7_8 - x_5_7) ≥ 1) ∧ ((x_5_8 - x_5_7) ≤ (t - 1)) ∧ ((x_7_8 - x_5_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_7) ∧ ((x_5_7 - x_7_8) ≥ 1) ∧ ((x_5_7 - x_5_8) ≤ (t - 1)) ∧ ((x_5_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_5_7 ≤ x_5_8) ∧ (x_5_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_5_8 + ((-1) * x_5_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_5_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_5_8) ∧ (x_5_8 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_5_7 + ((-1) * x_5_8)) ≤ ((-1) + t)) ∧ ((x_5_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_5_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_5_7 ≤ x_5_8) ↔ (((1) * x_5_7 + (-1) * x_5_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_5_8 ≤ x_7_8) ↔ (((1) * x_5_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 - x_5_7) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_5_8 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_8 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_5_8) ↔ (¬ (((1) * x_5_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_5_8 ≤ x_5_7) ↔ (¬ (((1) * x_5_7 + (-1) * x_5_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_5_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_5_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_5_7 - x_5_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_5_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_5_7)) ≥ 1) ↔ (((1) * x_5_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_5_8 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_7 + (-1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_5_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_5_7 + ((-1) * x_5_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_7 + (1) * x_5_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_5_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_5_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory173 (t x_1_5 x_1_7 x_5_7 : ℝ) : ((((x_1_5 ≤ x_1_7) ∧ (x_1_7 ≤ x_5_7) ∧ ((x_5_7 - x_1_5) ≥ 1) ∧ ((x_1_7 - x_1_5) ≤ (t - 1)) ∧ ((x_5_7 - x_1_7) ≤ (t - 1))) ∨ ((x_5_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_5) ∧ ((x_1_5 - x_5_7) ≥ 1) ∧ ((x_1_5 - x_1_7) ≤ (t - 1)) ∧ ((x_1_7 - x_5_7) ≤ (t - 1)))) ↔ (((x_1_5 ≤ x_1_7) ∧ (x_1_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_5_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_1_7) ↔ (((1) * x_1_5 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_7 ≤ x_5_7) ↔ (((1) * x_1_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_7 - x_1_5) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_7 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_7 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_5 - x_5_7) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_7 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory174 (t x_3_5 x_3_7 x_5_7 : ℝ) : ((((x_3_5 ≤ x_3_7) ∧ (x_3_7 ≤ x_5_7) ∧ ((x_5_7 - x_3_5) ≥ 1) ∧ ((x_3_7 - x_3_5) ≤ (t - 1)) ∧ ((x_5_7 - x_3_7) ≤ (t - 1))) ∨ ((x_5_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_5) ∧ ((x_3_5 - x_5_7) ≥ 1) ∧ ((x_3_5 - x_3_7) ≤ (t - 1)) ∧ ((x_3_7 - x_5_7) ≤ (t - 1)))) ↔ (((x_3_5 ≤ x_3_7) ∧ (x_3_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_3_7 + ((-1) * x_3_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_3_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_3_7) ∧ (x_3_7 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_3_5 + ((-1) * x_3_7)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_5_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_3_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_5 ≤ x_3_7) ↔ (((1) * x_3_5 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_3_7 ≤ x_5_7) ↔ (((1) * x_3_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_7 - x_3_5) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_3_7) ↔ (¬ (((1) * x_3_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_3_7 ≤ x_3_5) ↔ (¬ (((1) * x_3_5 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_5 - x_5_7) ≥ 1) ↔ (¬ (((1) * x_3_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_5 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_3_5)) ≥ 1) ↔ (((1) * x_3_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_5 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_5 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_5 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory175 (t x_4_7 x_4_8 x_7_8 : ℝ) : ((((x_4_7 ≤ x_4_8) ∧ (x_4_8 ≤ x_7_8) ∧ ((x_7_8 - x_4_7) ≥ 1) ∧ ((x_4_8 - x_4_7) ≤ (t - 1)) ∧ ((x_7_8 - x_4_8) ≤ (t - 1))) ∨ ((x_7_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_7) ∧ ((x_4_7 - x_7_8) ≥ 1) ∧ ((x_4_7 - x_4_8) ≤ (t - 1)) ∧ ((x_4_8 - x_7_8) ≤ (t - 1)))) ↔ (((x_4_7 ≤ x_4_8) ∧ (x_4_8 ≤ x_7_8) ∧ ((x_7_8 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_4_8 + ((-1) * x_4_7)) ≤ ((-1) + t)) ∧ ((x_7_8 + ((-1) * x_4_8)) ≤ ((-1) + t))) ∨ ((x_7_8 ≤ x_4_8) ∧ (x_4_8 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_7_8)) ≥ 1) ∧ ((x_4_7 + ((-1) * x_4_8)) ≤ ((-1) + t)) ∧ ((x_4_8 + ((-1) * x_7_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_7 + ((-1) * x_7_8)) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_7 ≤ x_4_8) ↔ (((1) * x_4_7 + (-1) * x_4_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_8 ≤ x_7_8) ↔ (((1) * x_4_8 + (-1) * x_7_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_7_8 - x_4_7) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_8 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_7_8 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_7_8 ≤ x_4_8) ↔ (¬ (((1) * x_4_8 + (-1) * x_7_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_8 ≤ x_4_7) ↔ (¬ (((1) * x_4_7 + (-1) * x_4_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_7 - x_7_8) ≥ 1) ↔ (¬ (((1) * x_4_7 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_7 - x_4_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_8 - x_7_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_7_8 + ((-1) * x_4_7)) ≥ 1) ↔ (((1) * x_4_7 + (-1) * x_7_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_8 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_7 + (-1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_7_8 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_8 + (-1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_7 + ((-1) * x_4_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_7 + (1) * x_4_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_8 + ((-1) * x_7_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_8 + (1) * x_7_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory176 (t x_4_7 : ℝ) : ((¬ (t ≤ x_4_7)) ↔ (¬ ((t + ((-1) * x_4_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_4_7) ↔ (((1) * t + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * t + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory177 (t x_1_4 x_1_7 x_4_7 : ℝ) : ((((x_1_4 ≤ x_1_7) ∧ (x_1_7 ≤ x_4_7) ∧ ((x_4_7 - x_1_4) ≥ 1) ∧ ((x_1_7 - x_1_4) ≤ (t - 1)) ∧ ((x_4_7 - x_1_7) ≤ (t - 1))) ∨ ((x_4_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_4) ∧ ((x_1_4 - x_4_7) ≥ 1) ∧ ((x_1_4 - x_1_7) ≤ (t - 1)) ∧ ((x_1_7 - x_4_7) ≤ (t - 1)))) ↔ (((x_1_4 ≤ x_1_7) ∧ (x_1_7 ≤ x_4_7) ∧ ((x_4_7 + ((-1) * x_1_4)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_4)) ≤ ((-1) + t)) ∧ ((x_4_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_4_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_4) ∧ ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((x_1_4 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_4_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_4 ≤ x_1_7) ↔ (((1) * x_1_4 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_4_7) ↔ (((1) * x_1_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_7 - x_1_4) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_7 - x_1_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_1_4) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_4 - x_4_7) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_4 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_4_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_7 + ((-1) * x_1_4)) ≥ 1) ↔ (((1) * x_1_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_7 + ((-1) * x_1_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_4 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_4_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory178 (t x_1_4 x_1_7 x_4_7 : ℝ) : ((((x_1_4 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_4_7)) ≤ 0) ∧ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1)) ∧ ((t + x_1_4 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_4_7)) ≤ (-1))) ∨ (¬ ((t + x_1_4 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≤ 0)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≤ 0))))) := by
  classical
  have e0 : ((x_1_7 + ((-1) * x_4_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_4_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_1_7 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_4_7)) ≤ (-1)) ↔ (((1) * x_1_4 + (-1) * x_4_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_4 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_4 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_4 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_4 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory179 (t x_1_4 x_1_7 x_4_7 : ℝ) : ((((x_1_7 + ((-1) * x_4_7)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ∧ ((t + ((-1) * x_1_4) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_4_7) ≥ 1)) ↔ (¬ ((¬ ((x_1_4 + ((-1) * x_4_7)) ≥ 1)) ∨ (¬ ((x_1_4 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_4) + x_1_7) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_7) + x_4_7) ≥ 1)) ∨ (¬ ((x_1_7 + ((-1) * x_4_7)) ≥ 0))))) := by
  classical
  have e0 : ((x_1_4 + ((-1) * x_4_7)) ≥ 1) ↔ (¬ (((1) * x_1_4 + (-1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_4_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_4_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_4 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_4 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_4) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_4 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_7) + x_4_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_4_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory180 (t x_5_7 : ℝ) : ((¬ (t ≤ x_5_7)) ↔ (¬ ((t + ((-1) * x_5_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_5_7) ↔ (((1) * t + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_5_7)) ≤ 0) ↔ (((1) * t + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory181 (t x_0_3 x_0_5 x_3_5 : ℝ) : ((((x_0_3 ≤ x_0_5) ∧ (x_0_5 ≤ x_3_5) ∧ ((x_3_5 - x_0_3) ≥ 1) ∧ ((x_0_5 - x_0_3) ≤ (t - 1)) ∧ ((x_3_5 - x_0_5) ≤ (t - 1))) ∨ ((x_3_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_3) ∧ ((x_0_3 - x_3_5) ≥ 1) ∧ ((x_0_3 - x_0_5) ≤ (t - 1)) ∧ ((x_0_5 - x_3_5) ≤ (t - 1)))) ↔ (((x_0_3 ≤ x_0_5) ∧ (x_0_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_0_3)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_0_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_0_5) ∧ (x_0_5 ≤ x_0_3) ∧ ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_0_3 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_0_5 + ((-1) * x_3_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_0_3 ≤ x_0_5) ↔ (((1) * x_0_3 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_5 ≤ x_3_5) ↔ (((1) * x_0_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 - x_0_3) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_5 - x_0_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_5 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_5 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_0_5 ≤ x_0_3) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_0_3 - x_3_5) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_3 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_5 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_5 + ((-1) * x_0_3)) ≥ 1) ↔ (((1) * x_0_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_0_5 + ((-1) * x_0_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_3 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory182 (t x_0_3 x_0_5 x_3_5 : ℝ) : ((((x_0_3 + ((-1) * x_0_5)) ≤ 0) ∧ ((x_0_5 + ((-1) * x_3_5)) ≤ 0) ∧ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1)) ∧ ((t + x_0_3 + ((-1) * x_0_5)) ≥ 1) ∧ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ↔ (¬ ((¬ ((t + x_0_3 + ((-1) * x_0_5)) ≥ 1)) ∨ (¬ ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≤ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≤ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_5)) ≤ (-1)))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_5)) ≤ (-1)) ↔ (((1) * x_0_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + x_0_3 + ((-1) * x_0_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_3 + (-1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((t + x_0_5 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_0_3 + ((-1) * x_0_5)) ≤ 0) ↔ (((1) * x_0_3 + (-1) * x_0_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_5 + ((-1) * x_3_5)) ≤ 0) ↔ (((1) * x_0_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory183 (t x_0_3 x_0_5 x_3_5 : ℝ) : ((((x_0_5 + ((-1) * x_3_5)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_0_5)) ≥ 0) ∧ ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((t + ((-1) * x_0_3) + x_0_5) ≥ 1) ∧ ((t + ((-1) * x_0_5) + x_3_5) ≥ 1)) ↔ (¬ ((¬ ((x_0_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_3) + x_0_5) ≥ 1)) ∨ (¬ ((t + ((-1) * x_0_5) + x_3_5) ≥ 1)) ∨ (¬ ((x_0_5 + ((-1) * x_3_5)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0))))) := by
  classical
  have e0 : ((x_0_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_0_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_0_5 + ((-1) * x_3_5)) ≥ 0) ↔ (¬ (((1) * x_0_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_0_3 + ((-1) * x_0_5)) ≥ 0) ↔ (¬ (((1) * x_0_3 + (-1) * x_0_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_0_3) + x_0_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_3 + (1) * x_0_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_0_5) + x_3_5) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory184 (x_0_3 x_0_5 x_0_6 x_3_6 : ℝ) : (¬ ((x_0_6 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_0_5)) ≥ 0)) ∨ (¬ ((x_0_5 + ((-1) * x_0_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

theorem theory185 (t x_4_9 : ℝ) : ((¬ (t ≤ x_4_9)) ↔ (¬ ((t + ((-1) * x_4_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_4_9) ↔ (((1) * t + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_4_9)) ≤ 0) ↔ (((1) * t + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory186 (t x_1_5 x_1_9 x_5_9 : ℝ) : ((((x_1_5 ≤ x_1_9) ∧ (x_1_9 ≤ x_5_9) ∧ ((x_5_9 - x_1_5) ≥ 1) ∧ ((x_1_9 - x_1_5) ≤ (t - 1)) ∧ ((x_5_9 - x_1_9) ≤ (t - 1))) ∨ ((x_5_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_5) ∧ ((x_1_5 - x_5_9) ≥ 1) ∧ ((x_1_5 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_5_9) ≤ (t - 1)))) ↔ (((x_1_5 ≤ x_1_9) ∧ (x_1_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_1_5)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_5) ∧ ((x_1_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_5_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_1_9) ↔ (((1) * x_1_5 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_9 ≤ x_5_9) ↔ (((1) * x_1_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_9 - x_1_5) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_9 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_5 - x_5_9) ≥ 1) ↔ (¬ (((1) * x_1_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_1_5)) ≥ 1) ↔ (((1) * x_1_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_5 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory187 (t x_4_5 x_4_9 x_5_9 : ℝ) : ((((x_4_5 ≤ x_4_9) ∧ (x_4_9 ≤ x_5_9) ∧ ((x_5_9 - x_4_5) ≥ 1) ∧ ((x_4_9 - x_4_5) ≤ (t - 1)) ∧ ((x_5_9 - x_4_9) ≤ (t - 1))) ∨ ((x_5_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_5) ∧ ((x_4_5 - x_5_9) ≥ 1) ∧ ((x_4_5 - x_4_9) ≤ (t - 1)) ∧ ((x_4_9 - x_5_9) ≤ (t - 1)))) ↔ (((x_4_5 ≤ x_4_9) ∧ (x_4_9 ≤ x_5_9) ∧ ((x_5_9 + ((-1) * x_4_5)) ≥ 1) ∧ ((x_4_9 + ((-1) * x_4_5)) ≤ ((-1) + t)) ∧ ((x_5_9 + ((-1) * x_4_9)) ≤ ((-1) + t))) ∨ ((x_5_9 ≤ x_4_9) ∧ (x_4_9 ≤ x_4_5) ∧ ((x_4_5 + ((-1) * x_5_9)) ≥ 1) ∧ ((x_4_5 + ((-1) * x_4_9)) ≤ ((-1) + t)) ∧ ((x_4_9 + ((-1) * x_5_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_4_5 + ((-1) * x_5_9)) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_4_5 ≤ x_4_9) ↔ (((1) * x_4_5 + (-1) * x_4_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_4_9 ≤ x_5_9) ↔ (((1) * x_4_9 + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_9 - x_4_5) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_9 - x_4_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_9 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_9 ≤ x_4_9) ↔ (¬ (((1) * x_4_9 + (-1) * x_5_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_4_9 ≤ x_4_5) ↔ (¬ (((1) * x_4_5 + (-1) * x_4_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_4_5 - x_5_9) ≥ 1) ↔ (¬ (((1) * x_4_5 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_4_5 - x_4_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_9 - x_5_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_9 + ((-1) * x_4_5)) ≥ 1) ↔ (((1) * x_4_5 + (-1) * x_5_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_9 + ((-1) * x_4_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_5 + (-1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_9 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_4_9 + (-1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_4_5 + ((-1) * x_4_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_5 + (1) * x_4_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_4_9 + ((-1) * x_5_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_4_9 + (1) * x_5_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory188 (t x_1_3 x_1_5 x_3_5 : ℝ) : ((((x_1_3 ≤ x_1_5) ∧ (x_1_5 ≤ x_3_5) ∧ ((x_3_5 - x_1_3) ≥ 1) ∧ ((x_1_5 - x_1_3) ≤ (t - 1)) ∧ ((x_3_5 - x_1_5) ≤ (t - 1))) ∨ ((x_3_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_3) ∧ ((x_1_3 - x_3_5) ≥ 1) ∧ ((x_1_3 - x_1_5) ≤ (t - 1)) ∧ ((x_1_5 - x_3_5) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_5) ∧ (x_1_5 ≤ x_3_5) ∧ ((x_3_5 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_5 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_5 + ((-1) * x_1_5)) ≤ ((-1) + t))) ∨ ((x_3_5 ≤ x_1_5) ∧ (x_1_5 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_5)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_5)) ≤ ((-1) + t)) ∧ ((x_1_5 + ((-1) * x_3_5)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_3 ≤ x_1_5) ↔ (((1) * x_1_3 + (-1) * x_1_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_5 ≤ x_3_5) ↔ (((1) * x_1_5 + (-1) * x_3_5) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_5 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_5 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_5 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_5 ≤ x_1_5) ↔ (¬ (((1) * x_1_5 + (-1) * x_3_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_5 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_5) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_3 - x_3_5) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_1_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_5 - x_3_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_5 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_5 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_5 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_5 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_5 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_3_5)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_5 + ((-1) * x_3_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_5 + (1) * x_3_5 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory189 (x_1_3 x_3_5 x_3_7 : ℝ) : (¬ ((x_3_5 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_3_5)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory190 (t x_6_7 : ℝ) : ((¬ (t ≤ x_6_7)) ↔ (¬ ((t + ((-1) * x_6_7)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_6_7) ↔ (((1) * t + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_6_7)) ≤ 0) ↔ (((1) * t + (-1) * x_6_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory191 (t x_2_3 x_2_8 x_3_8 : ℝ) : ((((x_2_3 ≤ x_2_8) ∧ (x_2_8 ≤ x_3_8) ∧ ((x_3_8 - x_2_3) ≥ 1) ∧ ((x_2_8 - x_2_3) ≤ (t - 1)) ∧ ((x_3_8 - x_2_8) ≤ (t - 1))) ∨ ((x_3_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_3) ∧ ((x_2_3 - x_3_8) ≥ 1) ∧ ((x_2_3 - x_2_8) ≤ (t - 1)) ∧ ((x_2_8 - x_3_8) ≤ (t - 1)))) ↔ (((x_2_3 ≤ x_2_8) ∧ (x_2_8 ≤ x_3_8) ∧ ((x_3_8 + ((-1) * x_2_3)) ≥ 1) ∧ ((x_2_8 + ((-1) * x_2_3)) ≤ ((-1) + t)) ∧ ((x_3_8 + ((-1) * x_2_8)) ≤ ((-1) + t))) ∨ ((x_3_8 ≤ x_2_8) ∧ (x_2_8 ≤ x_2_3) ∧ ((x_2_3 + ((-1) * x_3_8)) ≥ 1) ∧ ((x_2_3 + ((-1) * x_2_8)) ≤ ((-1) + t)) ∧ ((x_2_8 + ((-1) * x_3_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_2_3 ≤ x_2_8) ↔ (((1) * x_2_3 + (-1) * x_2_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_2_8 ≤ x_3_8) ↔ (((1) * x_2_8 + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_8 - x_2_3) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_2_8 - x_2_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_8 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_8 ≤ x_2_8) ↔ (¬ (((1) * x_2_8 + (-1) * x_3_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_2_8 ≤ x_2_3) ↔ (¬ (((1) * x_2_3 + (-1) * x_2_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_2_3 - x_3_8) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_2_3 - x_2_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_2_8 - x_3_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_8 + ((-1) * x_2_3)) ≥ 1) ↔ (((1) * x_2_3 + (-1) * x_3_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_2_8 + ((-1) * x_2_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_3 + (-1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_8 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_2_8 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_2_3 + ((-1) * x_3_8)) ≥ 1) ↔ (¬ (((1) * x_2_3 + (-1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_2_3 + ((-1) * x_2_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_3 + (1) * x_2_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_2_8 + ((-1) * x_3_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_2_8 + (1) * x_3_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory192 (t x_4_6 : ℝ) : ((¬ (t ≤ x_4_6)) ↔ (¬ ((t + ((-1) * x_4_6)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_4_6) ↔ (((1) * t + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_4_6)) ≤ 0) ↔ (((1) * t + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory193 (t x_3_4 x_3_6 x_4_6 : ℝ) : ((((x_3_4 ≤ x_3_6) ∧ (x_3_6 ≤ x_4_6) ∧ ((x_4_6 - x_3_4) ≥ 1) ∧ ((x_3_6 - x_3_4) ≤ (t - 1)) ∧ ((x_4_6 - x_3_6) ≤ (t - 1))) ∨ ((x_4_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_4) ∧ ((x_3_4 - x_4_6) ≥ 1) ∧ ((x_3_4 - x_3_6) ≤ (t - 1)) ∧ ((x_3_6 - x_4_6) ≤ (t - 1)))) ↔ (((x_3_4 ≤ x_3_6) ∧ (x_3_6 ≤ x_4_6) ∧ ((x_4_6 + ((-1) * x_3_4)) ≥ 1) ∧ ((x_3_6 + ((-1) * x_3_4)) ≤ ((-1) + t)) ∧ ((x_4_6 + ((-1) * x_3_6)) ≤ ((-1) + t))) ∨ ((x_4_6 ≤ x_3_6) ∧ (x_3_6 ≤ x_3_4) ∧ ((x_3_4 + ((-1) * x_4_6)) ≥ 1) ∧ ((x_3_4 + ((-1) * x_3_6)) ≤ ((-1) + t)) ∧ ((x_3_6 + ((-1) * x_4_6)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_3_4 ≤ x_3_6) ↔ (((1) * x_3_4 + (-1) * x_3_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_3_6 ≤ x_4_6) ↔ (((1) * x_3_6 + (-1) * x_4_6) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_4_6 - x_3_4) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_3_6 - x_3_4) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_4_6 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_4_6 ≤ x_3_6) ↔ (¬ (((1) * x_3_6 + (-1) * x_4_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_3_6 ≤ x_3_4) ↔ (¬ (((1) * x_3_4 + (-1) * x_3_6) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_3_4 - x_4_6) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_3_4 - x_3_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_3_6 - x_4_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_4_6 + ((-1) * x_3_4)) ≥ 1) ↔ (((1) * x_3_4 + (-1) * x_4_6 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_3_6 + ((-1) * x_3_4)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_4 + (-1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_4_6 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_3_6 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_3_4 + ((-1) * x_4_6)) ≥ 1) ↔ (¬ (((1) * x_3_4 + (-1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_3_4 + ((-1) * x_3_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_4 + (1) * x_3_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_3_6 + ((-1) * x_4_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_3_6 + (1) * x_4_6 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory194 (x_0_3 x_3_4 x_3_6 : ℝ) : (¬ ((x_3_4 + ((-1) * x_3_6)) ≥ 0)) ∨ (¬ ((x_0_3 + ((-1) * x_3_6)) ≤ (-1))) ∨ (¬ ((x_0_3 + ((-1) * x_3_4)) ≥ 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory195 (t x_1_3 x_1_7 x_3_7 : ℝ) : ((((x_1_3 ≤ x_1_7) ∧ (x_1_7 ≤ x_3_7) ∧ ((x_3_7 - x_1_3) ≥ 1) ∧ ((x_1_7 - x_1_3) ≤ (t - 1)) ∧ ((x_3_7 - x_1_7) ≤ (t - 1))) ∨ ((x_3_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_3) ∧ ((x_1_3 - x_3_7) ≥ 1) ∧ ((x_1_3 - x_1_7) ≤ (t - 1)) ∧ ((x_1_7 - x_3_7) ≤ (t - 1)))) ↔ (((x_1_3 ≤ x_1_7) ∧ (x_1_7 ≤ x_3_7) ∧ ((x_3_7 + ((-1) * x_1_3)) ≥ 1) ∧ ((x_1_7 + ((-1) * x_1_3)) ≤ ((-1) + t)) ∧ ((x_3_7 + ((-1) * x_1_7)) ≤ ((-1) + t))) ∨ ((x_3_7 ≤ x_1_7) ∧ (x_1_7 ≤ x_1_3) ∧ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((x_1_3 + ((-1) * x_1_7)) ≤ ((-1) + t)) ∧ ((x_1_7 + ((-1) * x_3_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_3 ≤ x_1_7) ↔ (((1) * x_1_3 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_7 ≤ x_3_7) ↔ (((1) * x_1_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_3_7 - x_1_3) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_7 - x_1_3) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_3_7 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_3_7 ≤ x_1_7) ↔ (¬ (((1) * x_1_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_7 ≤ x_1_3) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_3 - x_3_7) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_3 - x_1_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_7 - x_3_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_3_7 + ((-1) * x_1_3)) ≥ 1) ↔ (((1) * x_1_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_7 + ((-1) * x_1_3)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_3_7 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_3 + ((-1) * x_1_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_7 + ((-1) * x_3_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory196 (t x_1_3 x_1_7 x_3_7 : ℝ) : ((((x_1_3 + ((-1) * x_1_7)) ≤ 0) ∧ ((x_1_7 + ((-1) * x_3_7)) ≤ 0) ∧ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) ∧ ((t + x_1_3 + ((-1) * x_1_7)) ≥ 1) ∧ ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1)) ↔ (¬ ((¬ ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + x_1_3 + ((-1) * x_1_7)) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≤ (-1))) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≤ 0)) ∨ (¬ ((x_1_7 + ((-1) * x_3_7)) ≤ 0))))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_7)) ≤ (-1)) ↔ (((1) * x_1_3 + (-1) * x_3_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_3 + ((-1) * x_1_7)) ≤ 0) ↔ (((1) * x_1_3 + (-1) * x_1_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_7 + ((-1) * x_3_7)) ≤ 0) ↔ (((1) * x_1_7 + (-1) * x_3_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + x_1_7 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_7 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + x_1_3 + ((-1) * x_1_7)) ≥ 1) ↔ (¬ (((1) * t + (1) * x_1_3 + (-1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory197 (t x_1_3 x_1_7 x_3_7 : ℝ) : ((((x_1_7 + ((-1) * x_3_7)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_1_7)) ≥ 0) ∧ ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ∧ ((t + ((-1) * x_1_3) + x_1_7) ≥ 1) ∧ ((t + ((-1) * x_1_7) + x_3_7) ≥ 1)) ↔ (¬ ((¬ ((x_1_7 + ((-1) * x_3_7)) ≥ 0)) ∨ (¬ ((x_1_3 + ((-1) * x_1_7)) ≥ 0)) ∨ (¬ ((t + ((-1) * x_1_7) + x_3_7) ≥ 1)) ∨ (¬ ((x_1_3 + ((-1) * x_3_7)) ≥ 1)) ∨ (¬ ((t + ((-1) * x_1_3) + x_1_7) ≥ 1))))) := by
  classical
  have e0 : ((x_1_3 + ((-1) * x_3_7)) ≥ 1) ↔ (¬ (((1) * x_1_3 + (-1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((x_1_7 + ((-1) * x_3_7)) ≥ 0) ↔ (¬ (((1) * x_1_7 + (-1) * x_3_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_1_3 + ((-1) * x_1_7)) ≥ 0) ↔ (¬ (((1) * x_1_3 + (-1) * x_1_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((t + ((-1) * x_1_3) + x_1_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_3 + (1) * x_1_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((t + ((-1) * x_1_7) + x_3_7) ≥ 1) ↔ (¬ (((1) * t + (-1) * x_1_7 + (1) * x_3_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4]
  all_goals clear e0 e1 e2 e3 e4
  all_goals tauto

theorem theory198 (t x_3_8 : ℝ) : ((¬ (t ≤ x_3_8)) ↔ (¬ ((t + ((-1) * x_3_8)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_3_8) ↔ (((1) * t + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_3_8)) ≤ 0) ↔ (((1) * t + (-1) * x_3_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory199 (t x_5_9 : ℝ) : ((¬ (t ≤ x_5_9)) ↔ (¬ ((t + ((-1) * x_5_9)) ≤ 0))) := by
  classical
  have e0 : (t ≤ x_5_9) ↔ (((1) * t + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : ((t + ((-1) * x_5_9)) ≤ 0) ↔ (((1) * t + (-1) * x_5_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1]
  all_goals clear e0 e1
  all_goals tauto

theorem theory200 (t x_0_5 x_0_7 x_5_7 : ℝ) : ((((x_0_5 ≤ x_0_7) ∧ (x_0_7 ≤ x_5_7) ∧ ((x_5_7 - x_0_5) ≥ 1) ∧ ((x_0_7 - x_0_5) ≤ (t - 1)) ∧ ((x_5_7 - x_0_7) ≤ (t - 1))) ∨ ((x_5_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_5) ∧ ((x_0_5 - x_5_7) ≥ 1) ∧ ((x_0_5 - x_0_7) ≤ (t - 1)) ∧ ((x_0_7 - x_5_7) ≤ (t - 1)))) ↔ (((x_0_5 ≤ x_0_7) ∧ (x_0_7 ≤ x_5_7) ∧ ((x_5_7 + ((-1) * x_0_5)) ≥ 1) ∧ ((x_0_7 + ((-1) * x_0_5)) ≤ ((-1) + t)) ∧ ((x_5_7 + ((-1) * x_0_7)) ≤ ((-1) + t))) ∨ ((x_5_7 ≤ x_0_7) ∧ (x_0_7 ≤ x_0_5) ∧ ((x_0_5 + ((-1) * x_5_7)) ≥ 1) ∧ ((x_0_5 + ((-1) * x_0_7)) ≤ ((-1) + t)) ∧ ((x_0_7 + ((-1) * x_5_7)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_0_5 + ((-1) * x_5_7)) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_0_5 ≤ x_0_7) ↔ (((1) * x_0_5 + (-1) * x_0_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_0_7 ≤ x_5_7) ↔ (((1) * x_0_7 + (-1) * x_5_7) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_5_7 - x_0_5) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_0_7 - x_0_5) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_5_7 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_5_7 ≤ x_0_7) ↔ (¬ (((1) * x_0_7 + (-1) * x_5_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_0_7 ≤ x_0_5) ↔ (¬ (((1) * x_0_5 + (-1) * x_0_7) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_0_5 - x_5_7) ≥ 1) ↔ (¬ (((1) * x_0_5 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_0_5 - x_0_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_0_7 - x_5_7) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_5_7 + ((-1) * x_0_5)) ≥ 1) ↔ (((1) * x_0_5 + (-1) * x_5_7 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_0_7 + ((-1) * x_0_5)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_5 + (-1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_5_7 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_0_7 + (-1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_0_5 + ((-1) * x_0_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_5 + (1) * x_0_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_0_7 + ((-1) * x_5_7)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_0_7 + (1) * x_5_7 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory201 (x_0_2 x_2_4 x_2_5 : ℝ) : (¬ ((x_0_2 + ((-1) * x_2_5)) ≥ 1)) ∨ (¬ ((x_2_4 + ((-1) * x_2_5)) ≤ 0)) ∨ (¬ ((x_0_2 + ((-1) * x_2_4)) ≤ (-1))) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨h0, h1, h2⟩
  linarith

theorem theory202 (t x_1_6 x_1_8 x_6_8 : ℝ) : ((((x_1_6 ≤ x_1_8) ∧ (x_1_8 ≤ x_6_8) ∧ ((x_6_8 - x_1_6) ≥ 1) ∧ ((x_1_8 - x_1_6) ≤ (t - 1)) ∧ ((x_6_8 - x_1_8) ≤ (t - 1))) ∨ ((x_6_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_6) ∧ ((x_1_6 - x_6_8) ≥ 1) ∧ ((x_1_6 - x_1_8) ≤ (t - 1)) ∧ ((x_1_8 - x_6_8) ≤ (t - 1)))) ↔ (((x_1_6 ≤ x_1_8) ∧ (x_1_8 ≤ x_6_8) ∧ ((x_6_8 + ((-1) * x_1_6)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_6)) ≤ ((-1) + t)) ∧ ((x_6_8 + ((-1) * x_1_8)) ≤ ((-1) + t))) ∨ ((x_6_8 ≤ x_1_8) ∧ (x_1_8 ≤ x_1_6) ∧ ((x_1_6 + ((-1) * x_6_8)) ≥ 1) ∧ ((x_1_6 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_1_8 + ((-1) * x_6_8)) ≤ ((-1) + t))))) := by
  classical
  have e0 : (x_1_6 ≤ x_1_8) ↔ (((1) * x_1_6 + (-1) * x_1_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_6_8) ↔ (((1) * x_1_8 + (-1) * x_6_8) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : ((x_6_8 - x_1_6) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_1_8 - x_1_6) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_6_8 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : (x_6_8 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_6_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_1_8 ≤ x_1_6) ↔ (¬ (((1) * x_1_6 + (-1) * x_1_8) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : ((x_1_6 - x_6_8) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_6 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_6_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_6_8 + ((-1) * x_1_6)) ≥ 1) ↔ (((1) * x_1_6 + (-1) * x_6_8 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_1_8 + ((-1) * x_1_6)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_6 + (-1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_6_8 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_1_6 + ((-1) * x_6_8)) ≥ 1) ↔ (¬ (((1) * x_1_6 + (-1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_6 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_6 + (1) * x_1_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_8 + ((-1) * x_6_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_6_8 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

theorem theory203 (t x_1_8 x_1_9 x_8_9 : ℝ) : ((((x_1_8 ≤ x_1_9) ∧ (x_1_9 ≤ x_8_9) ∧ ((x_8_9 - x_1_8) ≥ 1) ∧ ((x_1_9 - x_1_8) ≤ (t - 1)) ∧ ((x_8_9 - x_1_9) ≤ (t - 1))) ∨ ((x_8_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_8) ∧ ((x_1_8 - x_8_9) ≥ 1) ∧ ((x_1_8 - x_1_9) ≤ (t - 1)) ∧ ((x_1_9 - x_8_9) ≤ (t - 1)))) ↔ (((x_1_8 ≤ x_1_9) ∧ (x_1_9 ≤ x_8_9) ∧ ((x_8_9 + ((-1) * x_1_8)) ≥ 1) ∧ ((x_1_9 + ((-1) * x_1_8)) ≤ ((-1) + t)) ∧ ((x_8_9 + ((-1) * x_1_9)) ≤ ((-1) + t))) ∨ ((x_8_9 ≤ x_1_9) ∧ (x_1_9 ≤ x_1_8) ∧ ((x_1_8 + ((-1) * x_8_9)) ≥ 1) ∧ ((x_1_8 + ((-1) * x_1_9)) ≤ ((-1) + t)) ∧ ((x_1_9 + ((-1) * x_8_9)) ≤ ((-1) + t))))) := by
  classical
  have e0 : ((x_1_8 + ((-1) * x_8_9)) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e1 : (x_1_8 ≤ x_1_9) ↔ (((1) * x_1_8 + (-1) * x_1_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e2 : (x_1_9 ≤ x_8_9) ↔ (((1) * x_1_9 + (-1) * x_8_9) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e3 : ((x_8_9 - x_1_8) ≥ 1) ↔ (((1) * x_1_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e4 : ((x_1_9 - x_1_8) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e5 : ((x_8_9 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e6 : (x_8_9 ≤ x_1_9) ↔ (¬ (((1) * x_1_9 + (-1) * x_8_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e7 : (x_1_9 ≤ x_1_8) ↔ (¬ (((1) * x_1_8 + (-1) * x_1_9) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e8 : ((x_1_8 - x_8_9) ≥ 1) ↔ (¬ (((1) * x_1_8 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e9 : ((x_1_8 - x_1_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e10 : ((x_1_9 - x_8_9) ≤ (t - 1)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e11 : ((x_8_9 + ((-1) * x_1_8)) ≥ 1) ↔ (((1) * x_1_8 + (-1) * x_8_9 + (1)) ≤ 0) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e12 : ((x_1_9 + ((-1) * x_1_8)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_8 + (-1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e13 : ((x_8_9 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (1) * x_1_9 + (-1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e14 : ((x_1_8 + ((-1) * x_1_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_8 + (1) * x_1_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  have e15 : ((x_1_9 + ((-1) * x_8_9)) ≤ ((-1) + t)) ↔ (¬ (((1) * t + (-1) * x_1_9 + (1) * x_8_9 + (-1)) < 0)) := by
    constructor <;> intro h <;> (try simp only [not_lt, not_le] at h ⊢) <;> linarith only [h]
  try simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  all_goals clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  all_goals tauto

end ElevenTheory
