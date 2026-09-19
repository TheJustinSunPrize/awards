import Mathlib.Basic.Real.Basic

/-!
JSP-000404 的有限方向约束。
方向模型沿用公开几何归约的数学定义，出处见 docs/选题核查.md。
十一点下界在本文件中是待证目标的定义。
-/
namespace SunPrize

def Triangle (t a b c : ℝ) : Prop :=
  (a ≤ b ∧ b ≤ c ∧ 1 ≤ c - a ∧ b - a ≤ t - 1 ∧ c - b ≤ t - 1) ∨
  (c ≤ b ∧ b ≤ a ∧ 1 ≤ a - c ∧ a - b ≤ t - 1 ∧ b - c ≤ t - 1)

structure DirectionModel (n : ℕ) (t : ℝ) where
  theta : Fin n → Fin n → ℝ
  range : ∀ i j, i < j → 0 ≤ theta i j ∧ theta i j < t
  triangle : ∀ i j k, i < j → j < k →
    Triangle t (theta i j) (theta i k) (theta j k)

def ElevenPointDirectionBound : Prop :=
  ∀ (t : ℝ), DirectionModel 11 t → 4 ≤ t

/-- 严格递增地选取标号，仍满足同一个方向模型。 -/
def DirectionModel.restrict {n k : ℕ} {t : ℝ} (m : DirectionModel n t)
    (f : Fin k → Fin n) (hf : ∀ ⦃i j⦄, i < j → f i < f j) : DirectionModel k t where
  theta i j := m.theta (f i) (f j)
  range i j hij := m.range (f i) (f j) (hf hij)
  triangle i j k hij hjk := m.triangle (f i) (f j) (f k) (hf hij) (hf hjk)

end SunPrize
