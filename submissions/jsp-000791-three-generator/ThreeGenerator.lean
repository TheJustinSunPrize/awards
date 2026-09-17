import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Exploratory component for JSP-000791 / Erdos 951.
This is a lower bound for three generators, not a counterexample or a solution
to the eventual prime-counting question. The elementary comparison argument
appears in Patrick White + Claude's public report of 28 July 2026,
https://www.erdosproblemaday.com/report/951, Section 2.
This file is a new Lean implementation, with that mathematical attribution.
-/

namespace JSP791

def monomial (a b c : ℝ) (u : Fin 3 → ℕ) : ℝ :=
  a ^ u 0 * b ^ u 1 * c ^ u 2

def Separated3 (a b c : ℝ) : Prop :=
  ∀ u v : Fin 3 → ℕ, u ≠ v → 1 ≤ |monomial a b c u - monomial a b c v|

theorem basic_comparisons {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) :
    2 ≤ a ∧ a + 1 ≤ b ∧ b + 1 ≤ c := by
  have h1 := hs ![1,0,0] ![0,0,0] (by decide)
  have h2 := hs ![0,1,0] ![1,0,0] (by decide)
  have h3 := hs ![0,0,1] ![0,1,0] (by decide)
  norm_num [monomial] at h1 h2 h3
  rw [abs_of_nonneg (by linarith)] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

theorem square_above_third {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) (hc : c < 5) : c + 1 ≤ a^2 := by
  obtain ⟨ha2, _, _⟩ := basic_comparisons ha hab hbc hs
  have h := hs ![2,0,0] ![0,0,1] (by decide)
  norm_num [monomial] at h
  rcases (le_abs.mp h) with h | h
  · linarith
  · nlinarith [sq_nonneg (a-2)]

/-- Every ordered separated triple has third generator at least
`(5 + sqrt 13)/2`. This does not assert existence at the lower bound. -/
theorem third_generator_lower {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) : (5 + Real.sqrt 13) / 2 ≤ c := by
  obtain ⟨ha2, hab1, hbc1⟩ := basic_comparisons ha hab hbc hs
  have hs0 := Real.sqrt_nonneg (13 : ℝ)
  have hsq : (Real.sqrt (13 : ℝ))^2 = 13 := Real.sq_sqrt (by norm_num)
  by_cases hc : c < 5
  · have ha_sq := square_above_third ha hab hbc hs hc
    have hprod : 0 ≤ (c-2-a)*(c-2+a) := mul_nonneg (by linarith) (by linarith)
    have hpoly : 0 ≤ c^2 - 5*c + 3 := by nlinarith
    by_contra hh
    have hsmall : 2*c-5 < Real.sqrt 13 := by linarith
    have hpos : 0 < Real.sqrt 13 + (2*c-5) := by linarith
    have hp := mul_pos (sub_pos.mpr hsmall) hpos
    nlinarith
  · have hs5 : Real.sqrt (13 : ℝ) < 5 := by nlinarith
    linarith

theorem third_generator_gt_43_div_10 {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) : (43 : ℝ)/10 < c := by
  have h := third_generator_lower ha hab hbc hs
  have hsq : (Real.sqrt (13 : ℝ))^2 = 13 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  have hl : (18 : ℝ)/5 < Real.sqrt 13 := by nlinarith
  linarith

/-- Two additional forced orientations used in the sharper three-generator bound. -/
theorem further_comparisons {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) (hc : c < (431 : ℝ)/100) :
    a*c + 1 ≤ b^2 ∧ a^2*b + 1 ≤ c^2 := by
  obtain ⟨ha2, hab1, hbc1⟩ := basic_comparisons ha hab hbc hs
  have hc43 := third_generator_gt_43_div_10 ha hab hbc hs
  have hb0 : 0 ≤ b := by linarith
  constructor
  · have h := hs ![0,2,0] ![1,0,1] (by decide)
    norm_num [monomial] at h
    rcases (le_abs.mp h) with h | h
    · linarith
    · have hsq := mul_nonneg (show 0 ≤ b-a-1 by linarith)
          (show 0 ≤ b+a+1 by linarith)
      have hp := mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ a-2 by linarith)
      have hlt := mul_pos (show 0 < a by linarith) (show 0 < 5-c by linarith)
      nlinarith
  · have h := hs ![0,0,2] ![2,1,0] (by decide)
    norm_num [monomial] at h
    rcases (le_abs.mp h) with h | h
    · linarith
    · have haub : a < (231 : ℝ)/100 := by linarith
      have hbub : b < (331 : ℝ)/100 := by linarith
      have ha_sq : a^2 ≤ (231 : ℝ)/100 * (231/100) := by
        nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr haub))
          (show 0 ≤ (231 : ℝ)/100+a by linarith)]
      have hp := mul_nonneg (sub_nonneg.mpr ha_sq) hb0
      nlinarith [sq_nonneg (c-43/10)]

end JSP791

#print axioms JSP791.third_generator_lower
#print axioms JSP791.third_generator_gt_43_div_10
#print axioms JSP791.further_comparisons
