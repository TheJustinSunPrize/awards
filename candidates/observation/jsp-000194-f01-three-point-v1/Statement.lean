import Mathlib

namespace JSP000194

/-- A point in the real affine plane. -/
abbrev Point := ℝ × ℝ

/-- The determinant criterion for three planar points to be collinear. -/
def Collinear (a b c : Point) : Prop :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0

/-- The geometric line represented by two distinct points, expressed by the
collinearity predicate. -/
def LineThrough (a b : Point) : Set Point := {x | Collinear a b x}

/-- The line through two distinct points is ordinary for `P` when no other
point of `P` lies on it. -/
def OrdinaryLine (P : Set Point) (a b : Point) : Prop :=
  a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ ∀ c ∈ P, Collinear a b c → c = a ∨ c = b

/-- The exact three-point specialization of the ordinary-line problem: every
pair among three distinct non-collinear points determines an ordinary line,
and the three represented lines are distinct. -/
def ThreePointOrdinary (a b c : Point) : Prop :=
  OrdinaryLine ({a, b, c} : Set Point) a b ∧
    OrdinaryLine ({a, b, c} : Set Point) a c ∧
      OrdinaryLine ({a, b, c} : Set Point) b c ∧
        LineThrough a b ≠ LineThrough a c ∧
          LineThrough a b ≠ LineThrough b c ∧
            LineThrough a c ≠ LineThrough b c

end JSP000194
