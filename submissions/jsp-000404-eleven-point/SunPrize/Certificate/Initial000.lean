import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule13 (p1 p7 : Prop) (h : (p1 ∨ p7)) : (p1) ∨ (p7) := by
  classical
  tauto

theorem initial13 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1) ∨ (meaning t m 7) := by
  have source : ((((m.theta 0 8) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 0 8)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 8)) ∧ (((m.theta 0 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 8 9 (by decide) (by decide)
  exact rule13 (meaning t m 1) (meaning t m 7) source

theorem rule26 (p13 p19 : Prop) (h : (p13 ∨ p19)) : (p13) ∨ (p19) := by
  classical
  tauto

theorem initial26 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 13) ∨ (meaning t m 19) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 2 8)) ∧ (((m.theta 2 8) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 2 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 8)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 2 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 8 (by decide) (by decide)
  exact rule26 (meaning t m 13) (meaning t m 19) source

theorem rule27 (p25 : Prop) (h : p25) : (p25) := by
  classical
  tauto

theorem initial27 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 25) := by
  have source : (t < 4) := by
    simpa only [Triangle] using ht
  exact rule27 (meaning t m 25) source

theorem rule40 (p26 p32 : Prop) (h : (p26 ∨ p32)) : (p26) ∨ (p32) := by
  classical
  tauto

theorem initial40 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 26) ∨ (meaning t m 32) := by
  have source : ((((m.theta 2 6) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 2 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 6 7 (by decide) (by decide)
  exact rule40 (meaning t m 26) (meaning t m 32) source

theorem rule53 (p38 p44 : Prop) (h : (p38 ∨ p44)) : (p38) ∨ (p44) := by
  classical
  tauto

theorem initial53 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 38) ∨ (meaning t m 44) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 5) - (m.theta 0 5)) ≤ (t - 1))) ∨ (((m.theta 2 5) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 0 5) - (m.theta 2 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 5 (by decide) (by decide)
  exact rule53 (meaning t m 38) (meaning t m 44) source

theorem rule66 (p50 p56 : Prop) (h : (p50 ∨ p56)) : (p50) ∨ (p56) := by
  classical
  tauto

theorem initial66 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 50) ∨ (meaning t m 56) := by
  have source : ((((m.theta 0 5) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 0 5)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 5 6) - (m.theta 0 6)) ≤ (t - 1))) ∨ (((m.theta 5 6) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 0 5)) ∧ (((m.theta 0 5) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 0 6) - (m.theta 5 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 5 6 (by decide) (by decide)
  exact rule66 (meaning t m 50) (meaning t m 56) source

theorem rule79 (p62 p68 : Prop) (h : (p62 ∨ p68)) : (p62) ∨ (p68) := by
  classical
  tauto

theorem initial79 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 62) ∨ (meaning t m 68) := by
  have source : ((((m.theta 1 5) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 1 5)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 5 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 5)) ∧ (((m.theta 1 5) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 5 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 5 8 (by decide) (by decide)
  exact rule79 (meaning t m 62) (meaning t m 68) source

theorem rule92 (p74 p80 : Prop) (h : (p74 ∨ p80)) : (p74) ∨ (p80) := by
  classical
  tauto

theorem initial92 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 74) ∨ (meaning t m 80) := by
  have source : ((((m.theta 6 7) ≤ (m.theta 6 8)) ∧ ((m.theta 6 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 6 8) - (m.theta 6 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 6 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 6 8)) ∧ ((m.theta 6 8) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 6 7) - (m.theta 6 8)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 7 8 (by decide) (by decide)
  exact rule92 (meaning t m 74) (meaning t m 80) source

theorem rule105 (p86 p92 : Prop) (h : (p86 ∨ p92)) : (p86) ∨ (p92) := by
  classical
  tauto

theorem initial105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 86) ∨ (meaning t m 92) := by
  have source : ((((m.theta 5 6) ≤ (m.theta 5 8)) ∧ ((m.theta 5 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 5 8) - (m.theta 5 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 5 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 5 8)) ∧ ((m.theta 5 8) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 5 6) - (m.theta 5 8)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 6 8 (by decide) (by decide)
  exact rule105 (meaning t m 86) (meaning t m 92) source

theorem rule118 (p98 p104 : Prop) (h : (p98 ∨ p104)) : (p98) ∨ (p104) := by
  classical
  tauto

theorem initial118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 98) ∨ (meaning t m 104) := by
  have source : ((((m.theta 1 5) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 1 5)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 5 6) - (m.theta 1 6)) ≤ (t - 1))) ∨ (((m.theta 5 6) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 1 5)) ∧ (((m.theta 1 5) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 1 6) - (m.theta 5 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 5 6 (by decide) (by decide)
  exact rule118 (meaning t m 98) (meaning t m 104) source

theorem rule131 (p110 p116 : Prop) (h : (p110 ∨ p116)) : (p110) ∨ (p116) := by
  classical
  tauto

theorem initial131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 110) ∨ (meaning t m 116) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 1 5)) ∧ (((m.theta 1 5) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 5) - (m.theta 0 5)) ≤ (t - 1))) ∨ (((m.theta 1 5) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 5)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 0 5) - (m.theta 1 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 5 (by decide) (by decide)
  exact rule131 (meaning t m 110) (meaning t m 116) source

theorem rule144 (p122 p128 : Prop) (h : (p122 ∨ p128)) : (p122) ∨ (p128) := by
  classical
  tauto

theorem initial144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 122) ∨ (meaning t m 128) := by
  have source : ((((m.theta 0 5) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 0 5)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 5 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 5)) ∧ (((m.theta 0 5) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 5 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 5 8 (by decide) (by decide)
  exact rule144 (meaning t m 122) (meaning t m 128) source

theorem rule157 (p134 p140 : Prop) (h : (p134 ∨ p140)) : (p134) ∨ (p140) := by
  classical
  tauto

theorem initial157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 134) ∨ (meaning t m 140) := by
  have source : ((((m.theta 0 4) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 0 4)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 4 5) - (m.theta 0 5)) ≤ (t - 1))) ∨ (((m.theta 4 5) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 0 4)) ∧ (((m.theta 0 4) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 0 5) - (m.theta 4 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 4 5 (by decide) (by decide)
  exact rule157 (meaning t m 134) (meaning t m 140) source

theorem rule170 (p146 p152 : Prop) (h : (p146 ∨ p152)) : (p146) ∨ (p152) := by
  classical
  tauto

theorem initial170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 146) ∨ (meaning t m 152) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 3)) ∧ ((m.theta 0 3) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 3) - (m.theta 0 3)) ≤ (t - 1))) ∨ (((m.theta 1 3) ≤ (m.theta 0 3)) ∧ ((m.theta 0 3) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 0 3) - (m.theta 1 3)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 3 (by decide) (by decide)
  exact rule170 (meaning t m 146) (meaning t m 152) source

theorem rule183 (p158 p164 : Prop) (h : (p158 ∨ p164)) : (p158) ∨ (p164) := by
  classical
  tauto

theorem initial183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 158) ∨ (meaning t m 164) := by
  have source : ((((m.theta 3 7) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 3 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 7 8 (by decide) (by decide)
  exact rule183 (meaning t m 158) (meaning t m 164) source

theorem rule196 (p170 p176 : Prop) (h : (p170 ∨ p176)) : (p170) ∨ (p176) := by
  classical
  tauto

theorem initial196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 170) ∨ (meaning t m 176) := by
  have source : ((((m.theta 5 6) ≤ (m.theta 5 7)) ∧ ((m.theta 5 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 5 7) - (m.theta 5 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 5 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 5 7)) ∧ ((m.theta 5 7) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 5 6) - (m.theta 5 7)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 6 7 (by decide) (by decide)
  exact rule196 (meaning t m 170) (meaning t m 176) source

theorem rule209 (p182 p188 : Prop) (h : (p182 ∨ p188)) : (p182) ∨ (p188) := by
  classical
  tauto

theorem initial209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 182) ∨ (meaning t m 188) := by
  have source : ((((m.theta 3 5) ≤ (m.theta 3 6)) ∧ ((m.theta 3 6) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 5 6) - (m.theta 3 6)) ≤ (t - 1))) ∨ (((m.theta 5 6) ≤ (m.theta 3 6)) ∧ ((m.theta 3 6) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 3 6) - (m.theta 5 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 5 6 (by decide) (by decide)
  exact rule209 (meaning t m 182) (meaning t m 188) source

theorem rule222 (p194 p200 : Prop) (h : (p194 ∨ p200)) : (p194) ∨ (p200) := by
  classical
  tauto

theorem initial222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 194) ∨ (meaning t m 200) := by
  have source : ((((m.theta 3 6) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 3 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 6 7 (by decide) (by decide)
  exact rule222 (meaning t m 194) (meaning t m 200) source

theorem rule235 (p206 p212 : Prop) (h : (p206 ∨ p212)) : (p206) ∨ (p212) := by
  classical
  tauto

theorem initial235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 206) ∨ (meaning t m 212) := by
  have source : ((((m.theta 0 6) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 0 6)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 6)) ∧ (((m.theta 0 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 6 7 (by decide) (by decide)
  exact rule235 (meaning t m 206) (meaning t m 212) source

theorem rule248 (p218 p224 : Prop) (h : (p218 ∨ p224)) : (p218) ∨ (p224) := by
  classical
  tauto

theorem initial248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 218) ∨ (meaning t m 224) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 6) - (m.theta 0 6)) ≤ (t - 1))) ∨ (((m.theta 3 6) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 0 6) - (m.theta 3 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 6 (by decide) (by decide)
  exact rule248 (meaning t m 218) (meaning t m 224) source

theorem rule261 (p230 p236 : Prop) (h : (p230 ∨ p236)) : (p230) ∨ (p236) := by
  classical
  tauto

theorem initial261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 230) ∨ (meaning t m 236) := by
  have source : ((((m.theta 0 7) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 0 7)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 7)) ∧ (((m.theta 0 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 7 8 (by decide) (by decide)
  exact rule261 (meaning t m 230) (meaning t m 236) source

theorem rule274 (p242 p248 : Prop) (h : (p242 ∨ p248)) : (p242) ∨ (p248) := by
  classical
  tauto

theorem initial274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 242) ∨ (meaning t m 248) := by
  have source : ((((m.theta 4 6) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 4 8) - (m.theta 4 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 4 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 4 6) - (m.theta 4 8)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 6 8 (by decide) (by decide)
  exact rule274 (meaning t m 242) (meaning t m 248) source

theorem rule287 (p254 p260 : Prop) (h : (p254 ∨ p260)) : (p254) ∨ (p260) := by
  classical
  tauto

theorem initial287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 254) ∨ (meaning t m 260) := by
  have source : ((((m.theta 6 8) ≤ (m.theta 6 9)) ∧ ((m.theta 6 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 6 9) - (m.theta 6 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 6 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 6 9)) ∧ ((m.theta 6 9) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 6 8) - (m.theta 6 9)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 8 9 (by decide) (by decide)
  exact rule287 (meaning t m 254) (meaning t m 260) source

theorem rule300 (p266 p272 : Prop) (h : (p266 ∨ p272)) : (p266) ∨ (p272) := by
  classical
  tauto

theorem initial300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 266) ∨ (meaning t m 272) := by
  have source : ((((m.theta 4 5) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 4 8) - (m.theta 4 5)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 4 8)) ≤ (t - 1))) ∨ (((m.theta 5 8) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 4 5) - (m.theta 4 8)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 5 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 5 8 (by decide) (by decide)
  exact rule300 (meaning t m 266) (meaning t m 272) source

theorem rule313 (p278 p284 : Prop) (h : (p278 ∨ p284)) : (p278) ∨ (p284) := by
  classical
  tauto

theorem initial313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 278) ∨ (meaning t m 284) := by
  have source : ((((m.theta 0 6) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 0 6)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 6)) ∧ (((m.theta 0 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 6 8 (by decide) (by decide)
  exact rule313 (meaning t m 278) (meaning t m 284) source

theorem rule326 (p290 p296 : Prop) (h : (p290 ∨ p296)) : (p290) ∨ (p296) := by
  classical
  tauto

theorem initial326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 290) ∨ (meaning t m 296) := by
  have source : ((((m.theta 6 7) ≤ (m.theta 6 9)) ∧ ((m.theta 6 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 6 9) - (m.theta 6 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 6 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 6 9)) ∧ ((m.theta 6 9) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 6 7) - (m.theta 6 9)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 7 9 (by decide) (by decide)
  exact rule326 (meaning t m 290) (meaning t m 296) source

theorem rule339 (p302 p308 : Prop) (h : (p302 ∨ p308)) : (p302) ∨ (p308) := by
  classical
  tauto

theorem initial339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 302) ∨ (meaning t m 308) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 5) - (m.theta 1 5)) ≤ (t - 1))) ∨ (((m.theta 4 5) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 1 5) - (m.theta 4 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 5 (by decide) (by decide)
  exact rule339 (meaning t m 302) (meaning t m 308) source

theorem rule352 (p314 p320 : Prop) (h : (p314 ∨ p320)) : (p314) ∨ (p320) := by
  classical
  tauto

theorem initial352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 314) ∨ (meaning t m 320) := by
  have source : ((((m.theta 4 7) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 4 9) - (m.theta 4 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 4 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 4 7) - (m.theta 4 9)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 7 9 (by decide) (by decide)
  exact rule352 (meaning t m 314) (meaning t m 320) source

theorem rule365 (p326 p332 : Prop) (h : (p326 ∨ p332)) : (p326) ∨ (p332) := by
  classical
  tauto

theorem initial365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 326) ∨ (meaning t m 332) := by
  have source : ((((m.theta 4 5) ≤ (m.theta 4 7)) ∧ ((m.theta 4 7) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 4 7) - (m.theta 4 5)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 4 7)) ≤ (t - 1))) ∨ (((m.theta 5 7) ≤ (m.theta 4 7)) ∧ ((m.theta 4 7) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 4 5) - (m.theta 4 7)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 5 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 5 7 (by decide) (by decide)
  exact rule365 (meaning t m 326) (meaning t m 332) source

theorem rule378 (p338 p344 : Prop) (h : (p338 ∨ p344)) : (p338) ∨ (p344) := by
  classical
  tauto

theorem initial378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 338) ∨ (meaning t m 344) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 3 7)) ≤ (t - 1))) ∨ (((m.theta 4 7) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 4 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 7 (by decide) (by decide)
  exact rule378 (meaning t m 338) (meaning t m 344) source

theorem rule391 (p350 p356 : Prop) (h : (p350 ∨ p356)) : (p350) ∨ (p356) := by
  classical
  tauto

theorem initial391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 350) ∨ (meaning t m 356) := by
  have source : ((((m.theta 3 7) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 3 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 7 9 (by decide) (by decide)
  exact rule391 (meaning t m 350) (meaning t m 356) source

theorem rule404 (p362 p368 : Prop) (h : (p362 ∨ p368)) : (p362) ∨ (p368) := by
  classical
  tauto

theorem initial404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 362) ∨ (meaning t m 368) := by
  have source : ((((m.theta 7 8) ≤ (m.theta 7 9)) ∧ ((m.theta 7 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 7 9) - (m.theta 7 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 7 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 7 9)) ∧ ((m.theta 7 9) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 7 8) - (m.theta 7 9)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 7 8 9 (by decide) (by decide)
  exact rule404 (meaning t m 362) (meaning t m 368) source

theorem rule417 (p374 p380 : Prop) (h : (p374 ∨ p380)) : (p374) ∨ (p380) := by
  classical
  tauto

theorem initial417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 374) ∨ (meaning t m 380) := by
  have source : ((((m.theta 0 4) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 0 4)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 4 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 4)) ∧ (((m.theta 0 4) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 4 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 4 8 (by decide) (by decide)
  exact rule417 (meaning t m 374) (meaning t m 380) source

theorem rule430 (p386 p392 : Prop) (h : (p386 ∨ p392)) : (p386) ∨ (p392) := by
  classical
  tauto

theorem initial430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 386) ∨ (meaning t m 392) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 6) - (m.theta 1 6)) ≤ (t - 1))) ∨ (((m.theta 4 6) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 1 6) - (m.theta 4 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 6 (by decide) (by decide)
  exact rule430 (meaning t m 386) (meaning t m 392) source

theorem rule443 (p398 p404 : Prop) (h : (p398 ∨ p404)) : (p398) ∨ (p404) := by
  classical
  tauto

theorem initial443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 398) ∨ (meaning t m 404) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 4 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 4 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 8 (by decide) (by decide)
  exact rule443 (meaning t m 398) (meaning t m 404) source

theorem rule456 (p410 p416 : Prop) (h : (p410 ∨ p416)) : (p410) ∨ (p416) := by
  classical
  tauto

theorem initial456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 410) ∨ (meaning t m 416) := by
  have source : ((((m.theta 4 8) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 4 9) - (m.theta 4 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 4 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 4 8) - (m.theta 4 9)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 8 9 (by decide) (by decide)
  exact rule456 (meaning t m 410) (meaning t m 416) source

theorem rule469 (p422 p428 : Prop) (h : (p422 ∨ p428)) : (p422) ∨ (p428) := by
  classical
  tauto

theorem initial469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 422) ∨ (meaning t m 428) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 5)) ∧ ((m.theta 3 5) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 5) - (m.theta 3 5)) ≤ (t - 1))) ∨ (((m.theta 4 5) ≤ (m.theta 3 5)) ∧ ((m.theta 3 5) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 3 5) - (m.theta 4 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 5 (by decide) (by decide)
  exact rule469 (meaning t m 422) (meaning t m 428) source

theorem rule482 (p434 p440 : Prop) (h : (p434 ∨ p440)) : (p434) ∨ (p440) := by
  classical
  tauto

theorem initial482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 434) ∨ (meaning t m 440) := by
  have source : ((((m.theta 4 6) ≤ (m.theta 4 7)) ∧ ((m.theta 4 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 4 7) - (m.theta 4 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 4 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 4 7)) ∧ ((m.theta 4 7) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 4 6) - (m.theta 4 7)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 6 7 (by decide) (by decide)
  exact rule482 (meaning t m 434) (meaning t m 440) source

theorem rule495 (p446 p452 : Prop) (h : (p446 ∨ p452)) : (p446) ∨ (p452) := by
  classical
  tauto

theorem initial495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 446) ∨ (meaning t m 452) := by
  have source : ((((m.theta 4 5) ≤ (m.theta 4 6)) ∧ ((m.theta 4 6) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 4 6) - (m.theta 4 5)) ≤ (t - 1)) ∧ (((m.theta 5 6) - (m.theta 4 6)) ≤ (t - 1))) ∨ (((m.theta 5 6) ≤ (m.theta 4 6)) ∧ ((m.theta 4 6) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 4 5) - (m.theta 4 6)) ≤ (t - 1)) ∧ (((m.theta 4 6) - (m.theta 5 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 5 6 (by decide) (by decide)
  exact rule495 (meaning t m 446) (meaning t m 452) source

theorem rule508 (p458 p464 : Prop) (h : (p458 ∨ p464)) : (p458) ∨ (p464) := by
  classical
  tauto

theorem initial508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 458) ∨ (meaning t m 464) := by
  have source : ((((m.theta 0 4) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 0 4)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 4 6) - (m.theta 0 6)) ≤ (t - 1))) ∨ (((m.theta 4 6) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 0 4)) ∧ (((m.theta 0 4) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 0 6) - (m.theta 4 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 4 6 (by decide) (by decide)
  exact rule508 (meaning t m 458) (meaning t m 464) source

theorem rule521 (p470 p476 : Prop) (h : (p470 ∨ p476)) : (p470) ∨ (p476) := by
  classical
  tauto

theorem initial521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 470) ∨ (meaning t m 476) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 4) - (m.theta 0 4)) ≤ (t - 1))) ∨ (((m.theta 2 4) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 0 4) - (m.theta 2 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 4 (by decide) (by decide)
  exact rule521 (meaning t m 470) (meaning t m 476) source

theorem rule534 (p482 p488 : Prop) (h : (p482 ∨ p488)) : (p482) ∨ (p488) := by
  classical
  tauto

theorem initial534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 482) ∨ (meaning t m 488) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 2)) ∧ ((m.theta 0 2) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 2) - (m.theta 0 2)) ≤ (t - 1))) ∨ (((m.theta 1 2) ≤ (m.theta 0 2)) ∧ ((m.theta 0 2) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 0 2) - (m.theta 1 2)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 2 (by decide) (by decide)
  exact rule534 (meaning t m 482) (meaning t m 488) source

theorem rule547 (p494 p500 : Prop) (h : (p494 ∨ p500)) : (p494) ∨ (p500) := by
  classical
  tauto

theorem initial547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 494) ∨ (meaning t m 500) := by
  have source : ((((m.theta 2 5) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 2 8)) ≤ (t - 1))) ∨ (((m.theta 5 8) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 5 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 5 8 (by decide) (by decide)
  exact rule547 (meaning t m 494) (meaning t m 500) source

theorem rule560 (p506 p512 : Prop) (h : (p506 ∨ p512)) : (p506) ∨ (p512) := by
  classical
  tauto

theorem initial560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 506) ∨ (meaning t m 512) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 4)) ∧ ((m.theta 2 4) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 4) - (m.theta 2 4)) ≤ (t - 1))) ∨ (((m.theta 3 4) ≤ (m.theta 2 4)) ∧ ((m.theta 2 4) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 2 4) - (m.theta 3 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 4 (by decide) (by decide)
  exact rule560 (meaning t m 506) (meaning t m 512) source

theorem rule573 (p518 p524 : Prop) (h : (p518 ∨ p524)) : (p518) ∨ (p524) := by
  classical
  tauto

theorem initial573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 518) ∨ (meaning t m 524) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 6) - (m.theta 1 6)) ≤ (t - 1))) ∨ (((m.theta 3 6) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 1 6) - (m.theta 3 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 6 (by decide) (by decide)
  exact rule573 (meaning t m 518) (meaning t m 524) source

theorem rule586 (p530 p536 : Prop) (h : (p530 ∨ p536)) : (p530) ∨ (p536) := by
  classical
  tauto

theorem initial586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 530) ∨ (meaning t m 536) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 4) - (m.theta 0 4)) ≤ (t - 1))) ∨ (((m.theta 3 4) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 0 4) - (m.theta 3 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 4 (by decide) (by decide)
  exact rule586 (meaning t m 530) (meaning t m 536) source

theorem rule599 (p542 p548 : Prop) (h : (p542 ∨ p548)) : (p542) ∨ (p548) := by
  classical
  tauto

theorem initial599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 542) ∨ (meaning t m 548) := by
  have source : ((((m.theta 3 6) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 3 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 6 8 (by decide) (by decide)
  exact rule599 (meaning t m 542) (meaning t m 548) source

theorem rule612 (p554 p560 : Prop) (h : (p554 ∨ p560)) : (p554) ∨ (p560) := by
  classical
  tauto

theorem initial612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 554) ∨ (meaning t m 560) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 2 7)) ≤ (t - 1))) ∨ (((m.theta 3 7) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 3 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 7 (by decide) (by decide)
  exact rule612 (meaning t m 554) (meaning t m 560) source

theorem rule625 (p566 p572 : Prop) (h : (p566 ∨ p572)) : (p566) ∨ (p572) := by
  classical
  tauto

theorem initial625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 566) ∨ (meaning t m 572) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 3)) ∧ ((m.theta 0 3) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 3) - (m.theta 0 3)) ≤ (t - 1))) ∨ (((m.theta 2 3) ≤ (m.theta 0 3)) ∧ ((m.theta 0 3) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 0 3) - (m.theta 2 3)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 3 (by decide) (by decide)
  exact rule625 (meaning t m 566) (meaning t m 572) source

theorem rule638 (p578 p584 : Prop) (h : (p578 ∨ p584)) : (p578) ∨ (p584) := by
  classical
  tauto

theorem initial638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 578) ∨ (meaning t m 584) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 2 7)) ∧ (((m.theta 2 7) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 1 7)) ≤ (t - 1))) ∨ (((m.theta 2 7) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 7)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 2 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 7 (by decide) (by decide)
  exact rule638 (meaning t m 578) (meaning t m 584) source

theorem rule651 (p590 p596 : Prop) (h : (p590 ∨ p596)) : (p590) ∨ (p596) := by
  classical
  tauto

theorem initial651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 590) ∨ (meaning t m 596) := by
  have source : ((((m.theta 2 7) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 2 7)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 2 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 2 7)) ∧ (((m.theta 2 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 7 8 (by decide) (by decide)
  exact rule651 (meaning t m 590) (meaning t m 596) source

theorem rule664 (p602 p608 : Prop) (h : (p602 ∨ p608)) : (p602) ∨ (p608) := by
  classical
  tauto

theorem initial664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 602) ∨ (meaning t m 608) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 4)) ∧ ((m.theta 1 4) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 4) - (m.theta 1 4)) ≤ (t - 1))) ∨ (((m.theta 3 4) ≤ (m.theta 1 4)) ∧ ((m.theta 1 4) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 1 4) - (m.theta 3 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 4 (by decide) (by decide)
  exact rule664 (meaning t m 602) (meaning t m 608) source

theorem rule677 (p614 p620 : Prop) (h : (p614 ∨ p620)) : (p614) ∨ (p620) := by
  classical
  tauto

theorem initial677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 614) ∨ (meaning t m 620) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 3)) ∧ ((m.theta 1 3) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 3) - (m.theta 1 3)) ≤ (t - 1))) ∨ (((m.theta 2 3) ≤ (m.theta 1 3)) ∧ ((m.theta 1 3) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 1 3) - (m.theta 2 3)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 3 (by decide) (by decide)
  exact rule677 (meaning t m 614) (meaning t m 620) source

theorem rule690 (p626 p632 : Prop) (h : (p626 ∨ p632)) : (p626) ∨ (p632) := by
  classical
  tauto

theorem initial690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 626) ∨ (meaning t m 632) := by
  have source : ((((m.theta 7 9) ≤ (m.theta 7 10)) ∧ ((m.theta 7 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 7 10) - (m.theta 7 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 7 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 7 10)) ∧ ((m.theta 7 10) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 7 9) - (m.theta 7 10)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 7 9 10 (by decide) (by decide)
  exact rule690 (meaning t m 626) (meaning t m 632) source

theorem rule703 (p638 p644 : Prop) (h : (p638 ∨ p644)) : (p638) ∨ (p644) := by
  classical
  tauto

theorem initial703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 638) ∨ (meaning t m 644) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 6) - (m.theta 0 6)) ≤ (t - 1))) ∨ (((m.theta 2 6) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 0 6) - (m.theta 2 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 6 (by decide) (by decide)
  exact rule703 (meaning t m 638) (meaning t m 644) source

theorem rule716 (p650 p656 : Prop) (h : (p650 ∨ p656)) : (p650) ∨ (p656) := by
  classical
  tauto

theorem initial716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 650) ∨ (meaning t m 656) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 6) - (m.theta 2 6)) ≤ (t - 1))) ∨ (((m.theta 3 6) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 2 6) - (m.theta 3 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 6 (by decide) (by decide)
  exact rule716 (meaning t m 650) (meaning t m 656) source

theorem rule729 (p662 p668 : Prop) (h : (p662 ∨ p668)) : (p662) ∨ (p668) := by
  classical
  tauto

theorem initial729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 662) ∨ (meaning t m 668) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 3 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 3 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 7 (by decide) (by decide)
  exact rule729 (meaning t m 662) (meaning t m 668) source

theorem rule742 (p674 p680 : Prop) (h : (p674 ∨ p680)) : (p674) ∨ (p680) := by
  classical
  tauto

theorem initial742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 674) ∨ (meaning t m 680) := by
  have source : ((((m.theta 2 6) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 2 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 6 8 (by decide) (by decide)
  exact rule742 (meaning t m 674) (meaning t m 680) source

theorem rule755 (p686 p692 : Prop) (h : (p686 ∨ p692)) : (p686) ∨ (p692) := by
  classical
  tauto

theorem initial755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 686) ∨ (meaning t m 692) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 6) - (m.theta 1 6)) ≤ (t - 1))) ∨ (((m.theta 2 6) ≤ (m.theta 1 6)) ∧ ((m.theta 1 6) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 1 6) - (m.theta 2 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 6 (by decide) (by decide)
  exact rule755 (meaning t m 686) (meaning t m 692) source

theorem rule768 (p698 p704 : Prop) (h : (p698 ∨ p704)) : (p698) ∨ (p704) := by
  classical
  tauto

theorem initial768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 698) ∨ (meaning t m 704) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 5) - (m.theta 1 5)) ≤ (t - 1))) ∨ (((m.theta 2 5) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 1 5) - (m.theta 2 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 5 (by decide) (by decide)
  exact rule768 (meaning t m 698) (meaning t m 704) source

theorem rule781 (p710 p716 : Prop) (h : (p710 ∨ p716)) : (p710) ∨ (p716) := by
  classical
  tauto

theorem initial781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 710) ∨ (meaning t m 716) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 5)) ∧ ((m.theta 2 5) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 5) - (m.theta 2 5)) ≤ (t - 1))) ∨ (((m.theta 4 5) ≤ (m.theta 2 5)) ∧ ((m.theta 2 5) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 2 5) - (m.theta 4 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 5 (by decide) (by decide)
  exact rule781 (meaning t m 710) (meaning t m 716) source

theorem rule794 (p722 p728 : Prop) (h : (p722 ∨ p728)) : (p722) ∨ (p728) := by
  classical
  tauto

theorem initial794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 722) ∨ (meaning t m 728) := by
  have source : ((((m.theta 2 5) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 5 6) - (m.theta 2 6)) ≤ (t - 1))) ∨ (((m.theta 5 6) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 2 6) - (m.theta 5 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 5 6 (by decide) (by decide)
  exact rule794 (meaning t m 722) (meaning t m 728) source

theorem rule807 (p734 p740 : Prop) (h : (p734 ∨ p740)) : (p734) ∨ (p740) := by
  classical
  tauto

theorem initial807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 734) ∨ (meaning t m 740) := by
  have source : ((((m.theta 2 5) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 2 7)) ≤ (t - 1))) ∨ (((m.theta 5 7) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 5 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 5 7 (by decide) (by decide)
  exact rule807 (meaning t m 734) (meaning t m 740) source

theorem rule820 (p746 p752 : Prop) (h : (p746 ∨ p752)) : (p746) ∨ (p752) := by
  classical
  tauto

theorem initial820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 746) ∨ (meaning t m 752) := by
  have source : ((((m.theta 5 7) ≤ (m.theta 5 8)) ∧ ((m.theta 5 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 5 8) - (m.theta 5 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 5 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 5 8)) ∧ ((m.theta 5 8) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 5 7) - (m.theta 5 8)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 7 8 (by decide) (by decide)
  exact rule820 (meaning t m 746) (meaning t m 752) source

theorem rule833 (p758 p764 : Prop) (h : (p758 ∨ p764)) : (p758) ∨ (p764) := by
  classical
  tauto

theorem initial833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 758) ∨ (meaning t m 764) := by
  have source : ((((m.theta 1 5) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 1 5)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 1 7)) ≤ (t - 1))) ∨ (((m.theta 5 7) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 1 5)) ∧ (((m.theta 1 5) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 5 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 5 7 (by decide) (by decide)
  exact rule833 (meaning t m 758) (meaning t m 764) source

theorem rule846 (p770 p776 : Prop) (h : (p770 ∨ p776)) : (p770) ∨ (p776) := by
  classical
  tauto

theorem initial846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 770) ∨ (meaning t m 776) := by
  have source : ((((m.theta 3 5) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 3 7)) ≤ (t - 1))) ∨ (((m.theta 5 7) ≤ (m.theta 3 7)) ∧ ((m.theta 3 7) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 5 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 5 7 (by decide) (by decide)
  exact rule846 (meaning t m 770) (meaning t m 776) source

theorem rule859 (p782 p788 : Prop) (h : (p782 ∨ p788)) : (p782) ∨ (p788) := by
  classical
  tauto

theorem initial859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 782) ∨ (meaning t m 788) := by
  have source : ((((m.theta 4 7) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 4 8) - (m.theta 4 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 4 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 4 8)) ∧ ((m.theta 4 8) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 4 7) - (m.theta 4 8)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 7 8 (by decide) (by decide)
  exact rule859 (meaning t m 782) (meaning t m 788) source

theorem rule872 (p794 p800 : Prop) (h : (p794 ∨ p800)) : (p794) ∨ (p800) := by
  classical
  tauto

theorem initial872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 794) ∨ (meaning t m 800) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 1 7)) ≤ (t - 1))) ∨ (((m.theta 4 7) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 4 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 7 (by decide) (by decide)
  exact rule872 (meaning t m 794) (meaning t m 800) source

theorem rule885 (p806 p812 : Prop) (h : (p806 ∨ p812)) : (p806) ∨ (p812) := by
  classical
  tauto

theorem initial885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 806) ∨ (meaning t m 812) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 5) - (m.theta 0 5)) ≤ (t - 1))) ∨ (((m.theta 3 5) ≤ (m.theta 0 5)) ∧ ((m.theta 0 5) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 0 5) - (m.theta 3 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 5 (by decide) (by decide)
  exact rule885 (meaning t m 806) (meaning t m 812) source

theorem rule898 (p818 p824 : Prop) (h : (p818 ∨ p824)) : (p818) ∨ (p824) := by
  classical
  tauto

theorem initial898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 818) ∨ (meaning t m 824) := by
  have source : ((((m.theta 1 5) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 1 5)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 5 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 5)) ∧ (((m.theta 1 5) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 5 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 5 9 (by decide) (by decide)
  exact rule898 (meaning t m 818) (meaning t m 824) source

theorem rule911 (p830 p836 : Prop) (h : (p830 ∨ p836)) : (p830) ∨ (p836) := by
  classical
  tauto

theorem initial911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 830) ∨ (meaning t m 836) := by
  have source : ((((m.theta 4 5) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 4 9) - (m.theta 4 5)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 4 9)) ≤ (t - 1))) ∨ (((m.theta 5 9) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 4 5) - (m.theta 4 9)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 5 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 5 9 (by decide) (by decide)
  exact rule911 (meaning t m 830) (meaning t m 836) source

theorem rule924 (p842 p848 : Prop) (h : (p842 ∨ p848)) : (p842) ∨ (p848) := by
  classical
  tauto

theorem initial924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 842) ∨ (meaning t m 848) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 5) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 5) - (m.theta 1 5)) ≤ (t - 1))) ∨ (((m.theta 3 5) ≤ (m.theta 1 5)) ∧ ((m.theta 1 5) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 5)) ≤ (t - 1)) ∧ (((m.theta 1 5) - (m.theta 3 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 5 (by decide) (by decide)
  exact rule924 (meaning t m 842) (meaning t m 848) source

theorem rule937 (p854 p860 : Prop) (h : (p854 ∨ p860)) : (p854) ∨ (p860) := by
  classical
  tauto

theorem initial937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 854) ∨ (meaning t m 860) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 3 8)) ∧ (((m.theta 3 8) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 2 8)) ≤ (t - 1))) ∨ (((m.theta 3 8) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 8)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 3 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 8 (by decide) (by decide)
  exact rule937 (meaning t m 854) (meaning t m 860) source

theorem rule950 (p866 p872 : Prop) (h : (p866 ∨ p872)) : (p866) ∨ (p872) := by
  classical
  tauto

theorem initial950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 866) ∨ (meaning t m 872) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 6)) ∧ ((m.theta 3 6) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 6) - (m.theta 3 6)) ≤ (t - 1))) ∨ (((m.theta 4 6) ≤ (m.theta 3 6)) ∧ ((m.theta 3 6) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 3 6) - (m.theta 4 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 6 (by decide) (by decide)
  exact rule950 (meaning t m 866) (meaning t m 872) source

theorem rule963 (p878 p884 : Prop) (h : (p878 ∨ p884)) : (p878) ∨ (p884) := by
  classical
  tauto

theorem initial963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 878) ∨ (meaning t m 884) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 7) - (m.theta 1 7)) ≤ (t - 1))) ∨ (((m.theta 3 7) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 3 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 7 (by decide) (by decide)
  exact rule963 (meaning t m 878) (meaning t m 884) source

theorem rule976 (p890 p896 : Prop) (h : (p890 ∨ p896)) : (p890) ∨ (p896) := by
  classical
  tauto

theorem initial976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 890) ∨ (meaning t m 896) := by
  have source : ((((m.theta 0 5) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 0 5)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 5 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 5 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 5)) ∧ (((m.theta 0 5) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 5 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 5 7 (by decide) (by decide)
  exact rule976 (meaning t m 890) (meaning t m 896) source

theorem rule989 (p902 p908 : Prop) (h : (p902 ∨ p908)) : (p902) ∨ (p908) := by
  classical
  tauto

theorem initial989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 902) ∨ (meaning t m 908) := by
  have source : ((((m.theta 1 6) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 1 6)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 6 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 6 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 6)) ∧ (((m.theta 1 6) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 6 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 6 8 (by decide) (by decide)
  exact rule989 (meaning t m 902) (meaning t m 908) source

theorem rule1002 (p914 p920 : Prop) (h : (p914 ∨ p920)) : (p914) ∨ (p920) := by
  classical
  tauto

theorem initial1002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 914) ∨ (meaning t m 920) := by
  have source : ((((m.theta 1 8) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 1 8)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 8)) ∧ (((m.theta 1 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 8 9 (by decide) (by decide)
  exact rule1002 (meaning t m 914) (meaning t m 920) source

theorem rule1015 (p926 p932 : Prop) (h : (p926 ∨ p932)) : (p926) ∨ (p932) := by
  classical
  tauto

theorem initial1015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 926) ∨ (meaning t m 932) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 3 8)) ≤ (t - 1))) ∨ (((m.theta 4 8) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 4 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 8 (by decide) (by decide)
  exact rule1015 (meaning t m 926) (meaning t m 932) source

theorem rule1028 (p938 p944 : Prop) (h : (p938 ∨ p944)) : (p938) ∨ (p944) := by
  classical
  tauto

theorem initial1028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 938) ∨ (meaning t m 944) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 1 6)) ∧ (((m.theta 1 6) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 6) - (m.theta 0 6)) ≤ (t - 1))) ∨ (((m.theta 1 6) ≤ (m.theta 0 6)) ∧ ((m.theta 0 6) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 6)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 0 6) - (m.theta 1 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 6 (by decide) (by decide)
  exact rule1028 (meaning t m 938) (meaning t m 944) source

theorem rule1041 (p950 p956 : Prop) (h : (p950 ∨ p956)) : (p950) ∨ (p956) := by
  classical
  tauto

theorem initial1041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 950) ∨ (meaning t m 956) := by
  have source : ((((m.theta 2 5) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 5 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 5 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 5 9 (by decide) (by decide)
  exact rule1041 (meaning t m 950) (meaning t m 956) source

theorem rule1054 (p962 p968 : Prop) (h : (p962 ∨ p968)) : (p962) ∨ (p968) := by
  classical
  tauto

theorem initial1054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 962) ∨ (meaning t m 968) := by
  have source : ((((m.theta 3 5) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 3 9)) ≤ (t - 1))) ∨ (((m.theta 5 9) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 5 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 5 9 (by decide) (by decide)
  exact rule1054 (meaning t m 962) (meaning t m 968) source

theorem rule1067 (p974 p980 : Prop) (h : (p974 ∨ p980)) : (p974) ∨ (p980) := by
  classical
  tauto

theorem initial1067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 974) ∨ (meaning t m 980) := by
  have source : ((((m.theta 5 6) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 5 9) - (m.theta 5 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 5 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 5 6) - (m.theta 5 9)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 6 9 (by decide) (by decide)
  exact rule1067 (meaning t m 974) (meaning t m 980) source

theorem rule1080 (p986 p992 : Prop) (h : (p986 ∨ p992)) : (p986) ∨ (p992) := by
  classical
  tauto

theorem initial1080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 986) ∨ (meaning t m 992) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 5)) ∧ ((m.theta 2 5) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 5) - (m.theta 2 5)) ≤ (t - 1))) ∨ (((m.theta 3 5) ≤ (m.theta 2 5)) ∧ ((m.theta 2 5) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 2 5) - (m.theta 3 5)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 5 (by decide) (by decide)
  exact rule1080 (meaning t m 986) (meaning t m 992) source

theorem rule1093 (p998 p1004 : Prop) (h : (p998 ∨ p1004)) : (p998) ∨ (p1004) := by
  classical
  tauto

theorem initial1093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 998) ∨ (meaning t m 1004) := by
  have source : ((((m.theta 5 8) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 5 9) - (m.theta 5 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 5 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 5 8) - (m.theta 5 9)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 8 9 (by decide) (by decide)
  exact rule1093 (meaning t m 998) (meaning t m 1004) source

theorem rule1106 (p1010 p1016 : Prop) (h : (p1010 ∨ p1016)) : (p1010) ∨ (p1016) := by
  classical
  tauto

theorem initial1106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1010) ∨ (meaning t m 1016) := by
  have source : ((((m.theta 3 5) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 5 8) - (m.theta 3 8)) ≤ (t - 1))) ∨ (((m.theta 5 8) ≤ (m.theta 3 8)) ∧ ((m.theta 3 8) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 5 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 5 8 (by decide) (by decide)
  exact rule1106 (meaning t m 1010) (meaning t m 1016) source

theorem rule1119 (p1022 p1028 : Prop) (h : (p1022 ∨ p1028)) : (p1022) ∨ (p1028) := by
  classical
  tauto

theorem initial1119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1022) ∨ (meaning t m 1028) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 3 8)) ∧ (((m.theta 3 8) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 3 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 8)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 3 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 8 (by decide) (by decide)
  exact rule1119 (meaning t m 1022) (meaning t m 1028) source

theorem rule1132 (p1034 p1040 : Prop) (h : (p1034 ∨ p1040)) : (p1034) ∨ (p1040) := by
  classical
  tauto

theorem initial1132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1034) ∨ (meaning t m 1040) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 3 8)) ∧ (((m.theta 3 8) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 3 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 8)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 3 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 8 (by decide) (by decide)
  exact rule1132 (meaning t m 1034) (meaning t m 1040) source

theorem rule1145 (p1046 p1052 : Prop) (h : (p1046 ∨ p1052)) : (p1046) ∨ (p1052) := by
  classical
  tauto

theorem initial1145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1046) ∨ (meaning t m 1052) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 2 7)) ≤ (t - 1))) ∨ (((m.theta 4 7) ≤ (m.theta 2 7)) ∧ ((m.theta 2 7) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 4 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 7 (by decide) (by decide)
  exact rule1145 (meaning t m 1046) (meaning t m 1052) source

theorem rule1158 (p1058 p1064 : Prop) (h : (p1058 ∨ p1064)) : (p1058) ∨ (p1064) := by
  classical
  tauto

theorem initial1158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1058) ∨ (meaning t m 1064) := by
  have source : ((((m.theta 0 5) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 0 5)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 5)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 5 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 5)) ∧ (((m.theta 0 5) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 0 5) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 5 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 5 9 (by decide) (by decide)
  exact rule1158 (meaning t m 1058) (meaning t m 1064) source

theorem rule1171 (p1070 p1076 : Prop) (h : (p1070 ∨ p1076)) : (p1070) ∨ (p1076) := by
  classical
  tauto

theorem initial1171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1070) ∨ (meaning t m 1076) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 4 9)) ∧ (((m.theta 4 9) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 4 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 9)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 4 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 9 (by decide) (by decide)
  exact rule1171 (meaning t m 1070) (meaning t m 1076) source

theorem rule1184 (p1082 p1088 : Prop) (h : (p1082 ∨ p1088)) : (p1082) ∨ (p1088) := by
  classical
  tauto

theorem initial1184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1082) ∨ (meaning t m 1088) := by
  have source : ((((m.theta 5 7) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 5 9) - (m.theta 5 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 5 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 5 9)) ∧ ((m.theta 5 9) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 5 7) - (m.theta 5 9)) ≤ (t - 1)) ∧ (((m.theta 5 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 7 9 (by decide) (by decide)
  exact rule1184 (meaning t m 1082) (meaning t m 1088) source

theorem rule1197 (p1094 p1100 : Prop) (h : (p1094 ∨ p1100)) : (p1094) ∨ (p1100) := by
  classical
  tauto

theorem initial1197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1094) ∨ (meaning t m 1100) := by
  have source : ((((m.theta 3 8) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 3 8)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 3 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 3 8)) ∧ (((m.theta 3 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 8 9 (by decide) (by decide)
  exact rule1197 (meaning t m 1094) (meaning t m 1100) source

theorem rule1210 (p1106 p1112 : Prop) (h : (p1106 ∨ p1112)) : (p1106) ∨ (p1112) := by
  classical
  tauto

theorem initial1210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1106) ∨ (meaning t m 1112) := by
  have source : ((((m.theta 8 9) ≤ (m.theta 8 10)) ∧ ((m.theta 8 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 8 10) - (m.theta 8 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 8 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 8 10)) ∧ ((m.theta 8 10) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 8 9) - (m.theta 8 10)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 8 9 10 (by decide) (by decide)
  exact rule1210 (meaning t m 1106) (meaning t m 1112) source

theorem rule1223 (p1118 p1124 : Prop) (h : (p1118 ∨ p1124)) : (p1118) ∨ (p1124) := by
  classical
  tauto

theorem initial1223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1118) ∨ (meaning t m 1124) := by
  have source : ((((m.theta 4 9) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 4 9)) ≥ 1) ∧ (((m.theta 4 10) - (m.theta 4 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 4 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 4 9)) ∧ (((m.theta 4 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 4 9) - (m.theta 4 10)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 9 10 (by decide) (by decide)
  exact rule1223 (meaning t m 1118) (meaning t m 1124) source

theorem rule1236 (p1130 p1136 : Prop) (h : (p1130 ∨ p1136)) : (p1130) ∨ (p1136) := by
  classical
  tauto

theorem initial1236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1130) ∨ (meaning t m 1136) := by
  have source : ((((m.theta 0 3) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 3 9)) ∧ (((m.theta 3 9) - (m.theta 0 3)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 3)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 3 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 3)) ∧ (((m.theta 0 3) - (m.theta 3 9)) ≥ 1) ∧ (((m.theta 0 3) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 3 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 3 9 (by decide) (by decide)
  exact rule1236 (meaning t m 1130) (meaning t m 1136) source

theorem rule1249 (p1142 p1148 : Prop) (h : (p1142 ∨ p1148)) : (p1142) ∨ (p1148) := by
  classical
  tauto

theorem initial1249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1142) ∨ (meaning t m 1148) := by
  have source : ((((m.theta 1 6) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 1 6)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 6 7) - (m.theta 1 7)) ≤ (t - 1))) ∨ (((m.theta 6 7) ≤ (m.theta 1 7)) ∧ ((m.theta 1 7) ≤ (m.theta 1 6)) ∧ (((m.theta 1 6) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 6 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 6 7 (by decide) (by decide)
  exact rule1249 (meaning t m 1142) (meaning t m 1148) source

theorem rule1262 (p1154 p1160 : Prop) (h : (p1154 ∨ p1160)) : (p1154) ∨ (p1160) := by
  classical
  tauto

theorem initial1262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1154) ∨ (meaning t m 1160) := by
  have source : ((((m.theta 1 6) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 1 6)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 6)) ∧ (((m.theta 1 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 6 9 (by decide) (by decide)
  exact rule1262 (meaning t m 1154) (meaning t m 1160) source

theorem rule1275 (p1166 p1172 : Prop) (h : (p1166 ∨ p1172)) : (p1166) ∨ (p1172) := by
  classical
  tauto

theorem initial1275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1166) ∨ (meaning t m 1172) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 4 9)) ∧ (((m.theta 4 9) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 4 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 9)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 4 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 9 (by decide) (by decide)
  exact rule1275 (meaning t m 1166) (meaning t m 1172) source

theorem rule1288 (p1178 p1184 : Prop) (h : (p1178 ∨ p1184)) : (p1178) ∨ (p1184) := by
  classical
  tauto

theorem initial1288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1178) ∨ (meaning t m 1184) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 4 9)) ∧ (((m.theta 4 9) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 3 9)) ≤ (t - 1))) ∨ (((m.theta 4 9) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 9)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 4 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 9 (by decide) (by decide)
  exact rule1288 (meaning t m 1178) (meaning t m 1184) source

theorem rule1301 (p1190 p1196 : Prop) (h : (p1190 ∨ p1196)) : (p1190) ∨ (p1196) := by
  classical
  tauto

theorem initial1301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1190) ∨ (meaning t m 1196) := by
  have source : ((((m.theta 0 4) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 4 9)) ∧ (((m.theta 4 9) - (m.theta 0 4)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 4 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 4)) ∧ (((m.theta 0 4) - (m.theta 4 9)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 4 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 4 9 (by decide) (by decide)
  exact rule1301 (meaning t m 1190) (meaning t m 1196) source

theorem rule1314 (p1202 p1208 : Prop) (h : (p1202 ∨ p1208)) : (p1202) ∨ (p1208) := by
  classical
  tauto

theorem initial1314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1202) ∨ (meaning t m 1208) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 4) - (m.theta 0 4)) ≤ (t - 1))) ∨ (((m.theta 1 4) ≤ (m.theta 0 4)) ∧ ((m.theta 0 4) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 0 4) - (m.theta 1 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 4 (by decide) (by decide)
  exact rule1314 (meaning t m 1202) (meaning t m 1208) source

theorem rule1327 (p1214 p1220 : Prop) (h : (p1214 ∨ p1220)) : (p1214) ∨ (p1220) := by
  classical
  tauto

theorem initial1327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1214) ∨ (meaning t m 1220) := by
  have source : ((((m.theta 0 4) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 0 4)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 4)) ≤ (t - 1)) ∧ (((m.theta 4 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 4 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 4)) ∧ (((m.theta 0 4) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 0 4) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 4 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 4 7 (by decide) (by decide)
  exact rule1327 (meaning t m 1214) (meaning t m 1220) source

theorem rule1340 (p1226 p1232 : Prop) (h : (p1226 ∨ p1232)) : (p1226) ∨ (p1232) := by
  classical
  tauto

theorem initial1340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1226) ∨ (meaning t m 1232) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 1 7)) ∧ (((m.theta 1 7) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 1 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 7)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 1 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 7 (by decide) (by decide)
  exact rule1340 (meaning t m 1226) (meaning t m 1232) source

theorem rule1353 (p1238 p1244 : Prop) (h : (p1238 ∨ p1244)) : (p1238) ∨ (p1244) := by
  classical
  tauto

theorem initial1353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1238) ∨ (meaning t m 1244) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 4)) ∧ ((m.theta 1 4) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 4) - (m.theta 1 4)) ≤ (t - 1))) ∨ (((m.theta 2 4) ≤ (m.theta 1 4)) ∧ ((m.theta 1 4) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 1 4) - (m.theta 2 4)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 4 (by decide) (by decide)
  exact rule1353 (meaning t m 1238) (meaning t m 1244) source

theorem rule1366 (p1250 p1256 : Prop) (h : (p1250 ∨ p1256)) : (p1250) ∨ (p1256) := by
  classical
  tauto

theorem initial1366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1250) ∨ (meaning t m 1256) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 6) - (m.theta 2 6)) ≤ (t - 1))) ∨ (((m.theta 4 6) ≤ (m.theta 2 6)) ∧ ((m.theta 2 6) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 2 6) - (m.theta 4 6)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 6 (by decide) (by decide)
  exact rule1366 (meaning t m 1250) (meaning t m 1256) source

theorem rule1379 (p1262 p1268 : Prop) (h : (p1262 ∨ p1268)) : (p1262) ∨ (p1268) := by
  classical
  tauto

theorem initial1379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1262) ∨ (meaning t m 1268) := by
  have source : ((((m.theta 2 7) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 2 7)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 7)) ∧ (((m.theta 2 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 7 9 (by decide) (by decide)
  exact rule1379 (meaning t m 1262) (meaning t m 1268) source

theorem rule1392 (p1274 p1280 : Prop) (h : (p1274 ∨ p1280)) : (p1274) ∨ (p1280) := by
  classical
  tauto

theorem initial1392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1274) ∨ (meaning t m 1280) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 1 8)) ∧ (((m.theta 1 8) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 0 8)) ≤ (t - 1))) ∨ (((m.theta 1 8) ≤ (m.theta 0 8)) ∧ ((m.theta 0 8) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 8)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 0 8) - (m.theta 1 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 8 (by decide) (by decide)
  exact rule1392 (meaning t m 1274) (meaning t m 1280) source

theorem rule1405 (p1286 p1292 : Prop) (h : (p1286 ∨ p1292)) : (p1286) ∨ (p1292) := by
  classical
  tauto

theorem initial1405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1286) ∨ (meaning t m 1292) := by
  have source : ((((m.theta 6 9) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 6 10) - (m.theta 6 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 6 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 6 9) - (m.theta 6 10)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 9 10 (by decide) (by decide)
  exact rule1405 (meaning t m 1286) (meaning t m 1292) source

theorem rule1418 (p1298 p1304 : Prop) (h : (p1298 ∨ p1304)) : (p1298) ∨ (p1304) := by
  classical
  tauto

theorem initial1418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1298) ∨ (meaning t m 1304) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 2 7)) ∧ (((m.theta 2 7) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 7) - (m.theta 0 7)) ≤ (t - 1))) ∨ (((m.theta 2 7) ≤ (m.theta 0 7)) ∧ ((m.theta 0 7) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 7)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 0 7) - (m.theta 2 7)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 7 (by decide) (by decide)
  exact rule1418 (meaning t m 1298) (meaning t m 1304) source

theorem rule1431 (p1310 p1316 : Prop) (h : (p1310 ∨ p1316)) : (p1310) ∨ (p1316) := by
  classical
  tauto

theorem initial1431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1310) ∨ (meaning t m 1316) := by
  have source : ((((m.theta 2 6) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 6 9 (by decide) (by decide)
  exact rule1431 (meaning t m 1310) (meaning t m 1316) source

theorem rule1444 (p1322 p1328 : Prop) (h : (p1322 ∨ p1328)) : (p1322) ∨ (p1328) := by
  classical
  tauto

theorem initial1444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1322) ∨ (meaning t m 1328) := by
  have source : ((((m.theta 3 6) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 3 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 3 9)) ∧ ((m.theta 3 9) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 6 9 (by decide) (by decide)
  exact rule1444 (meaning t m 1322) (meaning t m 1328) source

theorem rule1457 (p1334 p1340 : Prop) (h : (p1334 ∨ p1340)) : (p1334) ∨ (p1340) := by
  classical
  tauto

theorem initial1457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1334) ∨ (meaning t m 1340) := by
  have source : ((((m.theta 3 9) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 3 9)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 9)) ∧ (((m.theta 3 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 3 9) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 9 10 (by decide) (by decide)
  exact rule1457 (meaning t m 1334) (meaning t m 1340) source

theorem rule1470 (p1346 p1352 : Prop) (h : (p1346 ∨ p1352)) : (p1346) ∨ (p1352) := by
  classical
  tauto

theorem initial1470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1346) ∨ (meaning t m 1352) := by
  have source : ((((m.theta 0 7) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 0 7)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 7)) ∧ (((m.theta 0 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 7 9 (by decide) (by decide)
  exact rule1470 (meaning t m 1346) (meaning t m 1352) source

theorem rule1483 (p1358 p1364 : Prop) (h : (p1358 ∨ p1364)) : (p1358) ∨ (p1364) := by
  classical
  tauto

theorem initial1483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1358) ∨ (meaning t m 1364) := by
  have source : ((((m.theta 1 7) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 1 7)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 7 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 7 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 7)) ∧ (((m.theta 1 7) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 7 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 7 8 (by decide) (by decide)
  exact rule1483 (meaning t m 1358) (meaning t m 1364) source

theorem rule1496 (p1370 p1376 : Prop) (h : (p1370 ∨ p1376)) : (p1370) ∨ (p1376) := by
  classical
  tauto

theorem initial1496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1370) ∨ (meaning t m 1376) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 2 8)) ∧ (((m.theta 2 8) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 1 8)) ≤ (t - 1))) ∨ (((m.theta 2 8) ≤ (m.theta 1 8)) ∧ ((m.theta 1 8) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 8)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 1 8) - (m.theta 2 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 8 (by decide) (by decide)
  exact rule1496 (meaning t m 1370) (meaning t m 1376) source

theorem rule1509 (p1382 p1388 : Prop) (h : (p1382 ∨ p1388)) : (p1382) ∨ (p1388) := by
  classical
  tauto

theorem initial1509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1382) ∨ (meaning t m 1388) := by
  have source : ((((m.theta 4 6) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 4 9) - (m.theta 4 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 4 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 4 9)) ∧ ((m.theta 4 9) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 4 6) - (m.theta 4 9)) ≤ (t - 1)) ∧ (((m.theta 4 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 6 9 (by decide) (by decide)
  exact rule1509 (meaning t m 1382) (meaning t m 1388) source

theorem rule1522 (p1394 p1400 : Prop) (h : (p1394 ∨ p1400)) : (p1394) ∨ (p1400) := by
  classical
  tauto

theorem initial1522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1394) ∨ (meaning t m 1400) := by
  have source : ((((m.theta 1 2) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 2 9)) ∧ (((m.theta 2 9) - (m.theta 1 2)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 2)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 2 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 2)) ∧ (((m.theta 1 2) - (m.theta 2 9)) ≥ 1) ∧ (((m.theta 1 2) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 2 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 2 9 (by decide) (by decide)
  exact rule1522 (meaning t m 1394) (meaning t m 1400) source

theorem rule1535 (p1406 p1412 : Prop) (h : (p1406 ∨ p1412)) : (p1406) ∨ (p1412) := by
  classical
  tauto

theorem initial1535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1406) ∨ (meaning t m 1412) := by
  have source : ((((m.theta 2 8) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 8 9)) ∧ (((m.theta 8 9) - (m.theta 2 8)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 8 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 8 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 8)) ∧ (((m.theta 2 8) - (m.theta 8 9)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 8 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 8 9 (by decide) (by decide)
  exact rule1535 (meaning t m 1406) (meaning t m 1412) source

theorem rule1548 (p1418 p1424 : Prop) (h : (p1418 ∨ p1424)) : (p1418) ∨ (p1424) := by
  classical
  tauto

theorem initial1548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1418) ∨ (meaning t m 1424) := by
  have source : ((((m.theta 0 2) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 2 9)) ∧ (((m.theta 2 9) - (m.theta 0 2)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 2)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 2 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 2)) ∧ (((m.theta 0 2) - (m.theta 2 9)) ≥ 1) ∧ (((m.theta 0 2) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 2 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 2 9 (by decide) (by decide)
  exact rule1548 (meaning t m 1418) (meaning t m 1424) source

theorem rule1561 (p1430 p1436 : Prop) (h : (p1430 ∨ p1436)) : (p1430) ∨ (p1436) := by
  classical
  tauto

theorem initial1561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1430) ∨ (meaning t m 1436) := by
  have source : ((((m.theta 1 7) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 7 9)) ∧ (((m.theta 7 9) - (m.theta 1 7)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 7 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 7 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 7)) ∧ (((m.theta 1 7) - (m.theta 7 9)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 7 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 7 9 (by decide) (by decide)
  exact rule1561 (meaning t m 1430) (meaning t m 1436) source

theorem rule1574 (p1442 p1448 : Prop) (h : (p1442 ∨ p1448)) : (p1442) ∨ (p1448) := by
  classical
  tauto

theorem initial1574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1442) ∨ (meaning t m 1448) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 8) - (m.theta 2 8)) ≤ (t - 1))) ∨ (((m.theta 4 8) ≤ (m.theta 2 8)) ∧ ((m.theta 2 8) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 2 8) - (m.theta 4 8)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 8 (by decide) (by decide)
  exact rule1574 (meaning t m 1442) (meaning t m 1448) source

theorem rule1587 (p1454 p1460 : Prop) (h : (p1454 ∨ p1460)) : (p1454) ∨ (p1460) := by
  classical
  tauto

theorem initial1587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1454) ∨ (meaning t m 1460) := by
  have source : ((((m.theta 0 6) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 6 9)) ∧ (((m.theta 6 9) - (m.theta 0 6)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 6 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 6 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 6)) ∧ (((m.theta 0 6) - (m.theta 6 9)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 6 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 6 9 (by decide) (by decide)
  exact rule1587 (meaning t m 1454) (meaning t m 1460) source

theorem rule1600 (p1466 p1472 : Prop) (h : (p1466 ∨ p1472)) : (p1466) ∨ (p1472) := by
  classical
  tauto

theorem initial1600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1466) ∨ (meaning t m 1472) := by
  have source : ((((m.theta 2 9) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 2 9)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 9)) ∧ (((m.theta 2 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 9 10 (by decide) (by decide)
  exact rule1600 (meaning t m 1466) (meaning t m 1472) source

theorem rule1613 (p1478 p1484 : Prop) (h : (p1478 ∨ p1484)) : (p1478) ∨ (p1484) := by
  classical
  tauto

theorem initial1613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1478) ∨ (meaning t m 1484) := by
  have source : ((((m.theta 5 9) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 5 9)) ≥ 1) ∧ (((m.theta 5 10) - (m.theta 5 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 5 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 5 9)) ∧ (((m.theta 5 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 5 9) - (m.theta 5 10)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 9 10 (by decide) (by decide)
  exact rule1613 (meaning t m 1478) (meaning t m 1484) source

theorem rule1626 (p1490 p1496 : Prop) (h : (p1490 ∨ p1496)) : (p1490) ∨ (p1496) := by
  classical
  tauto

theorem initial1626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1490) ∨ (meaning t m 1496) := by
  have source : ((((m.theta 1 9) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 1 9)) ≥ 1) ∧ (((m.theta 1 10) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 1 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 1 9)) ∧ (((m.theta 1 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 10)) ≤ (t - 1)) ∧ (((m.theta 1 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 9 10 (by decide) (by decide)
  exact rule1626 (meaning t m 1490) (meaning t m 1496) source

theorem rule1639 (p1502 p1508 : Prop) (h : (p1502 ∨ p1508)) : (p1502) ∨ (p1508) := by
  classical
  tauto

theorem initial1639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1502) ∨ (meaning t m 1508) := by
  have source : ((((m.theta 2 5) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 5 10)) ∧ (((m.theta 5 10) - (m.theta 2 5)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 5)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 5 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 5)) ∧ (((m.theta 2 5) - (m.theta 5 10)) ≥ 1) ∧ (((m.theta 2 5) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 5 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 5 10 (by decide) (by decide)
  exact rule1639 (meaning t m 1502) (meaning t m 1508) source

theorem rule1652 (p1514 p1520 : Prop) (h : (p1514 ∨ p1520)) : (p1514) ∨ (p1520) := by
  classical
  tauto

theorem initial1652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1514) ∨ (meaning t m 1520) := by
  have source : ((((m.theta 4 5) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 5 10)) ∧ (((m.theta 5 10) - (m.theta 4 5)) ≥ 1) ∧ (((m.theta 4 10) - (m.theta 4 5)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 4 10)) ≤ (t - 1))) ∨ (((m.theta 5 10) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 4 5)) ∧ (((m.theta 4 5) - (m.theta 5 10)) ≥ 1) ∧ (((m.theta 4 5) - (m.theta 4 10)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 5 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 5 10 (by decide) (by decide)
  exact rule1652 (meaning t m 1514) (meaning t m 1520) source

theorem rule1665 (p1526 p1532 : Prop) (h : (p1526 ∨ p1532)) : (p1526) ∨ (p1532) := by
  classical
  tauto

theorem initial1665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1526) ∨ (meaning t m 1532) := by
  have source : ((((m.theta 5 6) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 5 6)) ≥ 1) ∧ (((m.theta 5 10) - (m.theta 5 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 5 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 5 6)) ∧ (((m.theta 5 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 5 6) - (m.theta 5 10)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 6 10 (by decide) (by decide)
  exact rule1665 (meaning t m 1526) (meaning t m 1532) source

theorem rule1678 (p1538 p1544 : Prop) (h : (p1538 ∨ p1544)) : (p1538) ∨ (p1544) := by
  classical
  tauto

theorem initial1678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1538) ∨ (meaning t m 1544) := by
  have source : ((((m.theta 2 3) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 3 9)) ∧ (((m.theta 3 9) - (m.theta 2 3)) ≥ 1) ∧ (((m.theta 2 9) - (m.theta 2 3)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 2 9)) ≤ (t - 1))) ∨ (((m.theta 3 9) ≤ (m.theta 2 9)) ∧ ((m.theta 2 9) ≤ (m.theta 2 3)) ∧ (((m.theta 2 3) - (m.theta 3 9)) ≥ 1) ∧ (((m.theta 2 3) - (m.theta 2 9)) ≤ (t - 1)) ∧ (((m.theta 2 9) - (m.theta 3 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 3 9 (by decide) (by decide)
  exact rule1678 (meaning t m 1538) (meaning t m 1544) source

theorem rule1691 (p1550 p1556 : Prop) (h : (p1550 ∨ p1556)) : (p1550) ∨ (p1556) := by
  classical
  tauto

theorem initial1691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1550) ∨ (meaning t m 1556) := by
  have source : ((((m.theta 0 9) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 9 10)) ∧ (((m.theta 9 10) - (m.theta 0 9)) ≥ 1) ∧ (((m.theta 0 10) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 9 10) - (m.theta 0 10)) ≤ (t - 1))) ∨ (((m.theta 9 10) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 0 9)) ∧ (((m.theta 0 9) - (m.theta 9 10)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 10)) ≤ (t - 1)) ∧ (((m.theta 0 10) - (m.theta 9 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 9 10 (by decide) (by decide)
  exact rule1691 (meaning t m 1550) (meaning t m 1556) source

theorem rule1704 (p1562 p1568 : Prop) (h : (p1562 ∨ p1568)) : (p1562) ∨ (p1568) := by
  classical
  tauto

theorem initial1704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1562) ∨ (meaning t m 1568) := by
  have source : ((((m.theta 6 7) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 6 7)) ≥ 1) ∧ (((m.theta 6 10) - (m.theta 6 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 6 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 6 7)) ∧ (((m.theta 6 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 6 7) - (m.theta 6 10)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 7 10 (by decide) (by decide)
  exact rule1704 (meaning t m 1562) (meaning t m 1568) source

theorem rule1717 (p1574 p1580 : Prop) (h : (p1574 ∨ p1580)) : (p1574) ∨ (p1580) := by
  classical
  tauto

theorem initial1717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1574) ∨ (meaning t m 1580) := by
  have source : ((((m.theta 1 4) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 4 10)) ∧ (((m.theta 4 10) - (m.theta 1 4)) ≥ 1) ∧ (((m.theta 1 10) - (m.theta 1 4)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 1 10)) ≤ (t - 1))) ∨ (((m.theta 4 10) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 1 4)) ∧ (((m.theta 1 4) - (m.theta 4 10)) ≥ 1) ∧ (((m.theta 1 4) - (m.theta 1 10)) ≤ (t - 1)) ∧ (((m.theta 1 10) - (m.theta 4 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 4 10 (by decide) (by decide)
  exact rule1717 (meaning t m 1574) (meaning t m 1580) source

theorem rule1730 (p1586 p1592 : Prop) (h : (p1586 ∨ p1592)) : (p1586) ∨ (p1592) := by
  classical
  tauto

theorem initial1730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1586) ∨ (meaning t m 1592) := by
  have source : ((((m.theta 0 1) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 1 9)) ∧ (((m.theta 1 9) - (m.theta 0 1)) ≥ 1) ∧ (((m.theta 0 9) - (m.theta 0 1)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 0 9)) ≤ (t - 1))) ∨ (((m.theta 1 9) ≤ (m.theta 0 9)) ∧ ((m.theta 0 9) ≤ (m.theta 0 1)) ∧ (((m.theta 0 1) - (m.theta 1 9)) ≥ 1) ∧ (((m.theta 0 1) - (m.theta 0 9)) ≤ (t - 1)) ∧ (((m.theta 0 9) - (m.theta 1 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 1 9 (by decide) (by decide)
  exact rule1730 (meaning t m 1586) (meaning t m 1592) source

theorem rule1743 (p1598 p1604 : Prop) (h : (p1598 ∨ p1604)) : (p1598) ∨ (p1604) := by
  classical
  tauto

theorem initial1743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1598) ∨ (meaning t m 1604) := by
  have source : ((((m.theta 1 3) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 3 9)) ∧ (((m.theta 3 9) - (m.theta 1 3)) ≥ 1) ∧ (((m.theta 1 9) - (m.theta 1 3)) ≤ (t - 1)) ∧ (((m.theta 3 9) - (m.theta 1 9)) ≤ (t - 1))) ∨ (((m.theta 3 9) ≤ (m.theta 1 9)) ∧ ((m.theta 1 9) ≤ (m.theta 1 3)) ∧ (((m.theta 1 3) - (m.theta 3 9)) ≥ 1) ∧ (((m.theta 1 3) - (m.theta 1 9)) ≤ (t - 1)) ∧ (((m.theta 1 9) - (m.theta 3 9)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 3 9 (by decide) (by decide)
  exact rule1743 (meaning t m 1598) (meaning t m 1604) source

theorem rule1756 (p1610 p1616 : Prop) (h : (p1610 ∨ p1616)) : (p1610) ∨ (p1616) := by
  classical
  tauto

theorem initial1756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1610) ∨ (meaning t m 1616) := by
  have source : ((((m.theta 4 7) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 4 7)) ≥ 1) ∧ (((m.theta 4 10) - (m.theta 4 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 4 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 4 7)) ∧ (((m.theta 4 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 4 7) - (m.theta 4 10)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 7 10 (by decide) (by decide)
  exact rule1756 (meaning t m 1610) (meaning t m 1616) source

theorem rule1769 (p1622 p1628 : Prop) (h : (p1622 ∨ p1628)) : (p1622) ∨ (p1628) := by
  classical
  tauto

theorem initial1769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1622) ∨ (meaning t m 1628) := by
  have source : ((((m.theta 4 6) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 4 6)) ≥ 1) ∧ (((m.theta 4 10) - (m.theta 4 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 4 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 4 6)) ∧ (((m.theta 4 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 4 6) - (m.theta 4 10)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 6 10 (by decide) (by decide)
  exact rule1769 (meaning t m 1622) (meaning t m 1628) source

theorem rule1782 (p1634 p1640 : Prop) (h : (p1634 ∨ p1640)) : (p1634) ∨ (p1640) := by
  classical
  tauto

theorem initial1782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1634) ∨ (meaning t m 1640) := by
  have source : ((((m.theta 3 4) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 4 10)) ∧ (((m.theta 4 10) - (m.theta 3 4)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 4)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 4 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 4)) ∧ (((m.theta 3 4) - (m.theta 4 10)) ≥ 1) ∧ (((m.theta 3 4) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 4 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 4 10 (by decide) (by decide)
  exact rule1782 (meaning t m 1634) (meaning t m 1640) source

theorem rule1795 (p1646 p1652 : Prop) (h : (p1646 ∨ p1652)) : (p1646) ∨ (p1652) := by
  classical
  tauto

theorem initial1795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1646) ∨ (meaning t m 1652) := by
  have source : ((((m.theta 2 6) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 2 6)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 6)) ∧ (((m.theta 2 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 2 6) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 6 10 (by decide) (by decide)
  exact rule1795 (meaning t m 1646) (meaning t m 1652) source

theorem rule1808 (p1658 p1664 : Prop) (h : (p1658 ∨ p1664)) : (p1658) ∨ (p1664) := by
  classical
  tauto

theorem initial1808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1658) ∨ (meaning t m 1664) := by
  have source : ((((m.theta 3 7) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 3 7)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 7)) ∧ (((m.theta 3 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 3 7) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 7 10 (by decide) (by decide)
  exact rule1808 (meaning t m 1658) (meaning t m 1664) source

theorem rule1821 (p1670 p1676 : Prop) (h : (p1670 ∨ p1676)) : (p1670) ∨ (p1676) := by
  classical
  tauto

theorem initial1821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1670) ∨ (meaning t m 1676) := by
  have source : ((((m.theta 7 8) ≤ (m.theta 7 10)) ∧ ((m.theta 7 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 7 8)) ≥ 1) ∧ (((m.theta 7 10) - (m.theta 7 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 7 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 7 10)) ∧ ((m.theta 7 10) ≤ (m.theta 7 8)) ∧ (((m.theta 7 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 7 8) - (m.theta 7 10)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 7 8 10 (by decide) (by decide)
  exact rule1821 (meaning t m 1670) (meaning t m 1676) source

theorem rule1834 (p1682 p1688 : Prop) (h : (p1682 ∨ p1688)) : (p1682) ∨ (p1688) := by
  classical
  tauto

theorem initial1834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1682) ∨ (meaning t m 1688) := by
  have source : ((((m.theta 5 8) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 5 8)) ≥ 1) ∧ (((m.theta 5 10) - (m.theta 5 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 5 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 5 8)) ∧ (((m.theta 5 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 5 8) - (m.theta 5 10)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 8 10 (by decide) (by decide)
  exact rule1834 (meaning t m 1682) (meaning t m 1688) source

theorem rule1847 (p1694 p1700 : Prop) (h : (p1694 ∨ p1700)) : (p1694) ∨ (p1700) := by
  classical
  tauto

theorem initial1847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1694) ∨ (meaning t m 1700) := by
  have source : ((((m.theta 6 8) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 6 8)) ≥ 1) ∧ (((m.theta 6 10) - (m.theta 6 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 6 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 6 10)) ∧ ((m.theta 6 10) ≤ (m.theta 6 8)) ∧ (((m.theta 6 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 6 8) - (m.theta 6 10)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 6 8 10 (by decide) (by decide)
  exact rule1847 (meaning t m 1694) (meaning t m 1700) source

theorem rule1860 (p1706 p1712 : Prop) (h : (p1706 ∨ p1712)) : (p1706) ∨ (p1712) := by
  classical
  tauto

theorem initial1860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1706) ∨ (meaning t m 1712) := by
  have source : ((((m.theta 0 8) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 0 8)) ≥ 1) ∧ (((m.theta 0 10) - (m.theta 0 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 0 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 0 8)) ∧ (((m.theta 0 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 0 8) - (m.theta 0 10)) ≤ (t - 1)) ∧ (((m.theta 0 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 8 10 (by decide) (by decide)
  exact rule1860 (meaning t m 1706) (meaning t m 1712) source

theorem rule1873 (p1718 p1724 : Prop) (h : (p1718 ∨ p1724)) : (p1718) ∨ (p1724) := by
  classical
  tauto

theorem initial1873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1718) ∨ (meaning t m 1724) := by
  have source : ((((m.theta 3 8) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 3 8)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 8)) ∧ (((m.theta 3 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 3 8) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 8 10 (by decide) (by decide)
  exact rule1873 (meaning t m 1718) (meaning t m 1724) source

theorem rule1886 (p1730 p1736 : Prop) (h : (p1730 ∨ p1736)) : (p1730) ∨ (p1736) := by
  classical
  tauto

theorem initial1886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1730) ∨ (meaning t m 1736) := by
  have source : ((((m.theta 2 8) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 2 8)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 8)) ∧ (((m.theta 2 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 2 8) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 8 10 (by decide) (by decide)
  exact rule1886 (meaning t m 1730) (meaning t m 1736) source

theorem rule1899 (p1742 p1748 : Prop) (h : (p1742 ∨ p1748)) : (p1742) ∨ (p1748) := by
  classical
  tauto

theorem initial1899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1742) ∨ (meaning t m 1748) := by
  have source : ((((m.theta 1 6) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 1 6)) ≥ 1) ∧ (((m.theta 1 10) - (m.theta 1 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 1 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 1 6)) ∧ (((m.theta 1 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 1 6) - (m.theta 1 10)) ≤ (t - 1)) ∧ (((m.theta 1 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 6 10 (by decide) (by decide)
  exact rule1899 (meaning t m 1742) (meaning t m 1748) source

theorem rule1912 (p1754 p1760 : Prop) (h : (p1754 ∨ p1760)) : (p1754) ∨ (p1760) := by
  classical
  tauto

theorem initial1912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1754) ∨ (meaning t m 1760) := by
  have source : ((((m.theta 0 7) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 0 7)) ≥ 1) ∧ (((m.theta 0 10) - (m.theta 0 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 0 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 0 7)) ∧ (((m.theta 0 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 0 7) - (m.theta 0 10)) ≤ (t - 1)) ∧ (((m.theta 0 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 7 10 (by decide) (by decide)
  exact rule1912 (meaning t m 1754) (meaning t m 1760) source

theorem rule1925 (p1766 p1772 : Prop) (h : (p1766 ∨ p1772)) : (p1766) ∨ (p1772) := by
  classical
  tauto

theorem initial1925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1766) ∨ (meaning t m 1772) := by
  have source : ((((m.theta 1 7) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 1 7)) ≥ 1) ∧ (((m.theta 1 10) - (m.theta 1 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 1 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 1 7)) ∧ (((m.theta 1 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 1 7) - (m.theta 1 10)) ≤ (t - 1)) ∧ (((m.theta 1 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 7 10 (by decide) (by decide)
  exact rule1925 (meaning t m 1766) (meaning t m 1772) source

theorem rule1938 (p1778 p1784 : Prop) (h : (p1778 ∨ p1784)) : (p1778) ∨ (p1784) := by
  classical
  tauto

theorem initial1938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1778) ∨ (meaning t m 1784) := by
  have source : ((((m.theta 0 6) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 0 6)) ≥ 1) ∧ (((m.theta 0 10) - (m.theta 0 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 0 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 0 10)) ∧ ((m.theta 0 10) ≤ (m.theta 0 6)) ∧ (((m.theta 0 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 0 6) - (m.theta 0 10)) ≤ (t - 1)) ∧ (((m.theta 0 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 0 6 10 (by decide) (by decide)
  exact rule1938 (meaning t m 1778) (meaning t m 1784) source

theorem rule1951 (p1790 p1796 : Prop) (h : (p1790 ∨ p1796)) : (p1790) ∨ (p1796) := by
  classical
  tauto

theorem initial1951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1790) ∨ (meaning t m 1796) := by
  have source : ((((m.theta 5 7) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 5 7)) ≥ 1) ∧ (((m.theta 5 10) - (m.theta 5 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 5 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 5 10)) ∧ ((m.theta 5 10) ≤ (m.theta 5 7)) ∧ (((m.theta 5 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 5 7) - (m.theta 5 10)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 5 7 10 (by decide) (by decide)
  exact rule1951 (meaning t m 1790) (meaning t m 1796) source

theorem rule1964 (p1802 p1808 : Prop) (h : (p1802 ∨ p1808)) : (p1802) ∨ (p1808) := by
  classical
  tauto

theorem initial1964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1802) ∨ (meaning t m 1808) := by
  have source : ((((m.theta 4 8) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 4 8)) ≥ 1) ∧ (((m.theta 4 10) - (m.theta 4 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 4 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 4 10)) ∧ ((m.theta 4 10) ≤ (m.theta 4 8)) ∧ (((m.theta 4 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 4 8) - (m.theta 4 10)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 4 8 10 (by decide) (by decide)
  exact rule1964 (meaning t m 1802) (meaning t m 1808) source

theorem rule1977 (p1814 p1820 : Prop) (h : (p1814 ∨ p1820)) : (p1814) ∨ (p1820) := by
  classical
  tauto

theorem initial1977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1814) ∨ (meaning t m 1820) := by
  have source : ((((m.theta 2 4) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 4 10)) ∧ (((m.theta 4 10) - (m.theta 2 4)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 4)) ≤ (t - 1)) ∧ (((m.theta 4 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 4 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 4)) ∧ (((m.theta 2 4) - (m.theta 4 10)) ≥ 1) ∧ (((m.theta 2 4) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 4 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 4 10 (by decide) (by decide)
  exact rule1977 (meaning t m 1814) (meaning t m 1820) source

theorem rule1990 (p1826 p1832 : Prop) (h : (p1826 ∨ p1832)) : (p1826) ∨ (p1832) := by
  classical
  tauto

theorem initial1990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1826) ∨ (meaning t m 1832) := by
  have source : ((((m.theta 1 8) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 8 10)) ∧ (((m.theta 8 10) - (m.theta 1 8)) ≥ 1) ∧ (((m.theta 1 10) - (m.theta 1 8)) ≤ (t - 1)) ∧ (((m.theta 8 10) - (m.theta 1 10)) ≤ (t - 1))) ∨ (((m.theta 8 10) ≤ (m.theta 1 10)) ∧ ((m.theta 1 10) ≤ (m.theta 1 8)) ∧ (((m.theta 1 8) - (m.theta 8 10)) ≥ 1) ∧ (((m.theta 1 8) - (m.theta 1 10)) ≤ (t - 1)) ∧ (((m.theta 1 10) - (m.theta 8 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 1 8 10 (by decide) (by decide)
  exact rule1990 (meaning t m 1826) (meaning t m 1832) source

theorem rule2016 (p1850 p1856 : Prop) (h : (p1850 ∨ p1856)) : (p1850) ∨ (p1856) := by
  classical
  tauto

theorem initial2016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1850) ∨ (meaning t m 1856) := by
  have source : ((((m.theta 3 6) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 6 10)) ∧ (((m.theta 6 10) - (m.theta 3 6)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 6)) ≤ (t - 1)) ∧ (((m.theta 6 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 6 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 6)) ∧ (((m.theta 3 6) - (m.theta 6 10)) ≥ 1) ∧ (((m.theta 3 6) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 6 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 6 10 (by decide) (by decide)
  exact rule2016 (meaning t m 1850) (meaning t m 1856) source

theorem rule2029 (p1862 p1868 : Prop) (h : (p1862 ∨ p1868)) : (p1862) ∨ (p1868) := by
  classical
  tauto

theorem initial2029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1862) ∨ (meaning t m 1868) := by
  have source : ((((m.theta 2 7) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 7 10)) ∧ (((m.theta 7 10) - (m.theta 2 7)) ≥ 1) ∧ (((m.theta 2 10) - (m.theta 2 7)) ≤ (t - 1)) ∧ (((m.theta 7 10) - (m.theta 2 10)) ≤ (t - 1))) ∨ (((m.theta 7 10) ≤ (m.theta 2 10)) ∧ ((m.theta 2 10) ≤ (m.theta 2 7)) ∧ (((m.theta 2 7) - (m.theta 7 10)) ≥ 1) ∧ (((m.theta 2 7) - (m.theta 2 10)) ≤ (t - 1)) ∧ (((m.theta 2 10) - (m.theta 7 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 2 7 10 (by decide) (by decide)
  exact rule2029 (meaning t m 1862) (meaning t m 1868) source

theorem rule2042 (p1874 p1880 : Prop) (h : (p1874 ∨ p1880)) : (p1874) ∨ (p1880) := by
  classical
  tauto

theorem initial2042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1874) ∨ (meaning t m 1880) := by
  have source : ((((m.theta 3 5) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 5 10)) ∧ (((m.theta 5 10) - (m.theta 3 5)) ≥ 1) ∧ (((m.theta 3 10) - (m.theta 3 5)) ≤ (t - 1)) ∧ (((m.theta 5 10) - (m.theta 3 10)) ≤ (t - 1))) ∨ (((m.theta 5 10) ≤ (m.theta 3 10)) ∧ ((m.theta 3 10) ≤ (m.theta 3 5)) ∧ (((m.theta 3 5) - (m.theta 5 10)) ≥ 1) ∧ (((m.theta 3 5) - (m.theta 3 10)) ≤ (t - 1)) ∧ (((m.theta 3 10) - (m.theta 5 10)) ≤ (t - 1)))) := by
    simpa only [Triangle] using m.triangle 3 5 10 (by decide) (by decide)
  exact rule2042 (meaning t m 1874) (meaning t m 1880) source

theorem rule2082 (p1922 : Prop) (h : p1922) : (p1922) := by
  classical
  tauto

theorem initial2082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1922) := by
  have source : ((m.theta 1 2) < t) := by
    simpa only [Triangle] using (m.range 1 2 (by decide)).2
  exact rule2082 (meaning t m 1922) source

theorem rule2083 (p1923 : Prop) (h : p1923) : (p1923) := by
  classical
  tauto

theorem initial2083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1923) := by
  have source : ((m.theta 0 5) < t) := by
    simpa only [Triangle] using (m.range 0 5 (by decide)).2
  exact rule2083 (meaning t m 1923) source

theorem rule2084 (p1924 : Prop) (h : p1924) : (p1924) := by
  classical
  tauto

theorem initial2084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1924) := by
  have source : ((m.theta 6 8) < t) := by
    simpa only [Triangle] using (m.range 6 8 (by decide)).2
  exact rule2084 (meaning t m 1924) source

theorem rule2085 (p1925 : Prop) (h : p1925) : (p1925) := by
  classical
  tauto

theorem initial2085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1925) := by
  have source : ((m.theta 4 5) < t) := by
    simpa only [Triangle] using (m.range 4 5 (by decide)).2
  exact rule2085 (meaning t m 1925) source

theorem rule2086 (p1926 : Prop) (h : p1926) : (p1926) := by
  classical
  tauto

theorem initial2086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1926) := by
  have source : ((m.theta 0 4) < t) := by
    simpa only [Triangle] using (m.range 0 4 (by decide)).2
  exact rule2086 (meaning t m 1926) source

theorem rule2087 (p1927 : Prop) (h : p1927) : (p1927) := by
  classical
  tauto

theorem initial2087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1927) := by
  have source : ((m.theta 3 6) < t) := by
    simpa only [Triangle] using (m.range 3 6 (by decide)).2
  exact rule2087 (meaning t m 1927) source

theorem rule2088 (p1928 : Prop) (h : p1928) : (p1928) := by
  classical
  tauto

theorem initial2088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1928) := by
  have source : ((m.theta 0 3) < t) := by
    simpa only [Triangle] using (m.range 0 3 (by decide)).2
  exact rule2088 (meaning t m 1928) source

theorem rule2089 (p1929 : Prop) (h : p1929) : (p1929) := by
  classical
  tauto

theorem initial2089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1929) := by
  have source : ((m.theta 0 6) < t) := by
    simpa only [Triangle] using (m.range 0 6 (by decide)).2
  exact rule2089 (meaning t m 1929) source

theorem rule2090 (p1930 : Prop) (h : p1930) : (p1930) := by
  classical
  tauto

theorem initial2090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1930) := by
  have source : ((m.theta 3 7) < t) := by
    simpa only [Triangle] using (m.range 3 7 (by decide)).2
  exact rule2090 (meaning t m 1930) source

theorem rule2091 (p1931 : Prop) (h : p1931) : (p1931) := by
  classical
  tauto

theorem initial2091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1931) := by
  have source : ((m.theta 3 5) < t) := by
    simpa only [Triangle] using (m.range 3 5 (by decide)).2
  exact rule2091 (meaning t m 1931) source

theorem rule2092 (p1932 : Prop) (h : p1932) : (p1932) := by
  classical
  tauto

theorem initial2092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1932) := by
  have source : ((m.theta 1 4) < t) := by
    simpa only [Triangle] using (m.range 1 4 (by decide)).2
  exact rule2092 (meaning t m 1932) source

theorem rule2093 (p1933 : Prop) (h : p1933) : (p1933) := by
  classical
  tauto

theorem initial2093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1933) := by
  have source : ((m.theta 7 9) < t) := by
    simpa only [Triangle] using (m.range 7 9 (by decide)).2
  exact rule2093 (meaning t m 1933) source

theorem rule2094 (p1934 : Prop) (h : p1934) : (p1934) := by
  classical
  tauto

theorem initial2094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1934) := by
  have source : ((m.theta 3 4) < t) := by
    simpa only [Triangle] using (m.range 3 4 (by decide)).2
  exact rule2094 (meaning t m 1934) source

theorem rule2095 (p1935 : Prop) (h : p1935) : (p1935) := by
  classical
  tauto

theorem initial2095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1935) := by
  have source : ((m.theta 0 2) < t) := by
    simpa only [Triangle] using (m.range 0 2 (by decide)).2
  exact rule2095 (meaning t m 1935) source

theorem rule2096 (p1936 : Prop) (h : p1936) : (p1936) := by
  classical
  tauto

theorem initial2096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1936) := by
  have source : ((m.theta 2 3) < t) := by
    simpa only [Triangle] using (m.range 2 3 (by decide)).2
  exact rule2096 (meaning t m 1936) source

theorem rule2097 (p1937 : Prop) (h : p1937) : (p1937) := by
  classical
  tauto

theorem initial2097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1937) := by
  have source : ((m.theta 7 8) < t) := by
    simpa only [Triangle] using (m.range 7 8 (by decide)).2
  exact rule2097 (meaning t m 1937) source

theorem rule2098 (p1938 : Prop) (h : p1938) : (p1938) := by
  classical
  tauto

theorem initial2098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1938) := by
  have source : ((m.theta 1 3) < t) := by
    simpa only [Triangle] using (m.range 1 3 (by decide)).2
  exact rule2098 (meaning t m 1938) source

theorem rule2099 (p1939 : Prop) (h : p1939) : (p1939) := by
  classical
  tauto

theorem initial2099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1939) := by
  have source : ((m.theta 0 1) < t) := by
    simpa only [Triangle] using (m.range 0 1 (by decide)).2
  exact rule2099 (meaning t m 1939) source

theorem rule2100 (p1940 : Prop) (h : p1940) : (p1940) := by
  classical
  tauto

theorem initial2100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1940) := by
  have source : ((m.theta 9 10) < t) := by
    simpa only [Triangle] using (m.range 9 10 (by decide)).2
  exact rule2100 (meaning t m 1940) source

theorem rule2101 (p1941 : Prop) (h : p1941) : (p1941) := by
  classical
  tauto

theorem initial2101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1941) := by
  have source : ((m.theta 5 6) < t) := by
    simpa only [Triangle] using (m.range 5 6 (by decide)).2
  exact rule2101 (meaning t m 1941) source

theorem rule2102 (p1942 : Prop) (h : p1942) : (p1942) := by
  classical
  tauto

theorem initial2102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1942) := by
  have source : ((m.theta 8 9) < t) := by
    simpa only [Triangle] using (m.range 8 9 (by decide)).2
  exact rule2102 (meaning t m 1942) source

theorem rule2103 (p1943 : Prop) (h : p1943) : (p1943) := by
  classical
  tauto

theorem initial2103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1943) := by
  have source : ((m.theta 2 4) < t) := by
    simpa only [Triangle] using (m.range 2 4 (by decide)).2
  exact rule2103 (meaning t m 1943) source

theorem rule2104 (p1944 : Prop) (h : p1944) : (p1944) := by
  classical
  tauto

theorem initial2104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1944) := by
  have source : ((m.theta 1 5) < t) := by
    simpa only [Triangle] using (m.range 1 5 (by decide)).2
  exact rule2104 (meaning t m 1944) source

theorem rule2105 (p1945 : Prop) (h : p1945) : (p1945) := by
  classical
  tauto

theorem initial2105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1945) := by
  have source : ((m.theta 4 7) < t) := by
    simpa only [Triangle] using (m.range 4 7 (by decide)).2
  exact rule2105 (meaning t m 1945) source

theorem rule2106 (p1946 : Prop) (h : p1946) : (p1946) := by
  classical
  tauto

theorem initial2106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1946) := by
  have source : ((m.theta 5 7) < t) := by
    simpa only [Triangle] using (m.range 5 7 (by decide)).2
  exact rule2106 (meaning t m 1946) source

theorem rule2107 (p1947 : Prop) (h : p1947) : (p1947) := by
  classical
  tauto

theorem initial2107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1947) := by
  have source : ((m.theta 4 9) < t) := by
    simpa only [Triangle] using (m.range 4 9 (by decide)).2
  exact rule2107 (meaning t m 1947) source

theorem rule2108 (p1948 : Prop) (h : p1948) : (p1948) := by
  classical
  tauto

theorem initial2108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1948) := by
  have source : ((m.theta 6 7) < t) := by
    simpa only [Triangle] using (m.range 6 7 (by decide)).2
  exact rule2108 (meaning t m 1948) source

theorem rule2109 (p1949 : Prop) (h : p1949) : (p1949) := by
  classical
  tauto

theorem initial2109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1949) := by
  have source : ((m.theta 4 6) < t) := by
    simpa only [Triangle] using (m.range 4 6 (by decide)).2
  exact rule2109 (meaning t m 1949) source

theorem rule2110 (p1950 : Prop) (h : p1950) : (p1950) := by
  classical
  tauto

theorem initial2110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1950) := by
  have source : ((m.theta 3 8) < t) := by
    simpa only [Triangle] using (m.range 3 8 (by decide)).2
  exact rule2110 (meaning t m 1950) source

theorem rule2111 (p1951 : Prop) (h : p1951) : (p1951) := by
  classical
  tauto

theorem initial2111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1951) := by
  have source : ((m.theta 5 9) < t) := by
    simpa only [Triangle] using (m.range 5 9 (by decide)).2
  exact rule2111 (meaning t m 1951) source

theorem rule2112 (p1952 : Prop) (h : p1952) : (p1952) := by
  classical
  tauto

theorem initial2112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1952) := by
  have source : ((m.theta 6 9) < t) := by
    simpa only [Triangle] using (m.range 6 9 (by decide)).2
  exact rule2112 (meaning t m 1952) source

theorem rule2113 (p1953 : Prop) (h : p1953) : (p1953) := by
  classical
  tauto

theorem initial2113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1953) := by
  have source : ((m.theta 0 7) < t) := by
    simpa only [Triangle] using (m.range 0 7 (by decide)).2
  exact rule2113 (meaning t m 1953) source

theorem rule2114 (p1954 : Prop) (h : p1954) : (p1954) := by
  classical
  tauto

theorem initial2114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1954) := by
  have source : ((m.theta 2 7) < t) := by
    simpa only [Triangle] using (m.range 2 7 (by decide)).2
  exact rule2114 (meaning t m 1954) source

theorem rule2115 (p1955 : Prop) (h : p1955) : (p1955) := by
  classical
  tauto

theorem initial2115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1955) := by
  have source : ((m.theta 1 8) < t) := by
    simpa only [Triangle] using (m.range 1 8 (by decide)).2
  exact rule2115 (meaning t m 1955) source

theorem rule2116 (p1956 : Prop) (h : p1956) : (p1956) := by
  classical
  tauto

theorem initial2116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1956) := by
  have source : ((m.theta 2 5) < t) := by
    simpa only [Triangle] using (m.range 2 5 (by decide)).2
  exact rule2116 (meaning t m 1956) source

theorem rule2117 (p1957 : Prop) (h : p1957) : (p1957) := by
  classical
  tauto

theorem initial2117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1957) := by
  have source : ((m.theta 4 8) < t) := by
    simpa only [Triangle] using (m.range 4 8 (by decide)).2
  exact rule2117 (meaning t m 1957) source

theorem rule2118 (p1958 : Prop) (h : p1958) : (p1958) := by
  classical
  tauto

theorem initial2118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1958) := by
  have source : ((m.theta 5 8) < t) := by
    simpa only [Triangle] using (m.range 5 8 (by decide)).2
  exact rule2118 (meaning t m 1958) source

theorem rule2119 (p1959 : Prop) (h : p1959) : (p1959) := by
  classical
  tauto

theorem initial2119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1959) := by
  have source : ((m.theta 2 6) < t) := by
    simpa only [Triangle] using (m.range 2 6 (by decide)).2
  exact rule2119 (meaning t m 1959) source

theorem rule2120 (p1960 : Prop) (h : p1960) : (p1960) := by
  classical
  tauto

theorem initial2120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1960) := by
  have source : ((m.theta 2 9) < t) := by
    simpa only [Triangle] using (m.range 2 9 (by decide)).2
  exact rule2120 (meaning t m 1960) source

theorem rule2121 (p1961 : Prop) (h : p1961) : (p1961) := by
  classical
  tauto

theorem initial2121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1961) := by
  have source : ((m.theta 1 7) < t) := by
    simpa only [Triangle] using (m.range 1 7 (by decide)).2
  exact rule2121 (meaning t m 1961) source

theorem rule2122 (p1962 : Prop) (h : p1962) : (p1962) := by
  classical
  tauto

theorem initial2122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1962) := by
  have source : ((m.theta 0 9) < t) := by
    simpa only [Triangle] using (m.range 0 9 (by decide)).2
  exact rule2122 (meaning t m 1962) source

theorem rule2123 (p1963 : Prop) (h : p1963) : (p1963) := by
  classical
  tauto

theorem initial2123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1963) := by
  have source : ((m.theta 1 6) < t) := by
    simpa only [Triangle] using (m.range 1 6 (by decide)).2
  exact rule2123 (meaning t m 1963) source

theorem rule2124 (p1964 : Prop) (h : p1964) : (p1964) := by
  classical
  tauto

theorem initial2124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 1964) := by
  have source : ((m.theta 3 9) < t) := by
    simpa only [Triangle] using (m.range 3 9 (by decide)).2
  exact rule2124 (meaning t m 1964) source

end SunPrize.SMT
