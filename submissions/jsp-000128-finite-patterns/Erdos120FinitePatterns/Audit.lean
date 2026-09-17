import Erdos120FinitePatterns

open Set MeasureTheory

namespace Erdos120FinitePatterns.Audit

/-- Literal target definition from the pinned Formal Conjectures statement. -/
def ReferenceErdos120For (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  MeasurableSet E ∧ 0 < volume E ∧
    ∀ a b : ℝ, a ≠ 0 → ¬ .image (fun x => a * x + b) A ⊆ E

example (A : Set ℝ) : ReferenceErdos120For A ↔ Erdos120For A := Iff.rfl

/-- The exact finite-set variant, with its independently repeated definition. -/
theorem exact_statement {A : Set ℝ} (h : A.Finite) :
    ¬ ReferenceErdos120For A := finite_set h

/-- Explicit quantifiers and the original nonzero-scale requirement. -/
theorem affine_copy (A E : Set ℝ) (hA : A.Finite) (hE : MeasurableSet E)
    (hpos : 0 < volume E) :
    ∃ a b : ℝ, a ≠ 0 ∧ ∀ x ∈ A, a * x + b ∈ E := by
  obtain ⟨a, ha, b, hsub⟩ := finite_pattern hA hE hpos
  exact ⟨a, b, ha.ne', fun x hx ↦ hsub ⟨x, hx, rfl⟩⟩

#print axioms Erdos120FinitePatterns.compact_finite_pattern
#print axioms Erdos120FinitePatterns.finite_pattern
#print axioms Erdos120FinitePatterns.finite_set
#print axioms exact_statement
#print axioms affine_copy

end Erdos120FinitePatterns.Audit
