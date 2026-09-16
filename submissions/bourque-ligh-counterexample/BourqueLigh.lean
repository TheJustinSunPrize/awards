import Mathlib

/-!
# A counterexample to the Bourque–Ligh conjecture

The counterexample is the set published in:
P. Haukkanen, J. Wang and J. Sillanpää, *On Smith's determinant*,
Linear Algebra and its Applications 258 (1997), 251–269.

We verify closure under greatest common divisors and exhibit an explicit
nonzero integer vector in the kernel of the least-common-multiple matrix.
-/

namespace BourqueLigh

open Matrix

/-- A finite set is gcd-closed when it contains the gcd of any two of its elements. -/
def GCDClosed (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, Nat.gcd a b ∈ S

/-- The least-common-multiple matrix, indexed by the elements of the set itself. -/
def lcmMatrix (S : Finset ℕ) : Matrix S S ℤ :=
  fun a b => (Nat.lcm a.val b.val : ℤ)

/-- The same least-common-multiple matrix over the real numbers. -/
def lcmMatrixReal (S : Finset ℕ) : Matrix S S ℝ :=
  fun a b => (Nat.lcm a.val b.val : ℝ)

/-- The Bourque–Ligh conjecture (1992). -/
def conjecture : Prop :=
  ∀ S : Finset ℕ, (∀ x ∈ S, 0 < x) → GCDClosed S → (lcmMatrix S).det ≠ 0

/-- The nonsingularity formulation over the real numbers. -/
def realConjecture : Prop :=
  ∀ S : Finset ℕ, (∀ x ∈ S, 0 < x) → GCDClosed S → (lcmMatrixReal S).det ≠ 0

/-- The nine-element counterexample of Haukkanen, Wang and Sillanpää. -/
def counterexample : Finset ℕ := {1, 2, 3, 4, 5, 6, 10, 45, 180}

theorem counterexample_card : counterexample.card = 9 := by decide

theorem counterexample_positive : ∀ x ∈ counterexample, 0 < x := by decide

theorem counterexample_gcdClosed : GCDClosed counterexample := by
  unfold GCDClosed
  decide

/-- Coefficients of an integer relation among the columns of the LCM matrix. -/
def kernelVector (a : counterexample) : ℤ :=
  match a.val with
  | 1 => -180
  | 2 => 180
  | 3 => 60
  | 4 => -45
  | 5 => 36
  | 6 => -30
  | 10 => -18
  | 45 => -4
  | _ => 1

theorem kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have := congrFun h ⟨180, by decide⟩
  norm_num [kernelVector] at this

theorem lcmMatrix_mulVec_kernelVector : lcmMatrix counterexample *ᵥ kernelVector = 0 := by
  decide

theorem counterexample_det_eq_zero : (lcmMatrix counterexample).det = 0 := by
  by_contra h
  exact kernelVector_ne_zero
    (Matrix.eq_zero_of_mulVec_eq_zero h lcmMatrix_mulVec_kernelVector)

/-- The original universal nonsingularity conjecture is false. -/
theorem not_conjecture : ¬ conjecture := by
  intro h
  exact h counterexample counterexample_positive counterexample_gcdClosed
    counterexample_det_eq_zero

theorem lcmMatrixReal_det (S : Finset ℕ) :
    (lcmMatrixReal S).det = ((lcmMatrix S).det : ℝ) := by
  simpa [lcmMatrixReal, lcmMatrix] using (Int.cast_det (lcmMatrix S) (R := ℝ)).symm

theorem counterexample_real_det_eq_zero : (lcmMatrixReal counterexample).det = 0 := by
  rw [lcmMatrixReal_det, counterexample_det_eq_zero, Int.cast_zero]

theorem not_realConjecture : ¬ realConjecture := by
  intro h
  exact h counterexample counterexample_positive counterexample_gcdClosed
    counterexample_real_det_eq_zero

/-- A finite set of nine distinct positive integers disproves the conjecture. -/
theorem exists_gcdClosed_singular_lcmMatrix :
    ∃ S : Finset ℕ, S.card = 9 ∧ (∀ x ∈ S, 0 < x) ∧ GCDClosed S ∧
      (lcmMatrixReal S).det = 0 :=
  ⟨counterexample, counterexample_card, counterexample_positive,
    counterexample_gcdClosed, counterexample_real_det_eq_zero⟩

#print axioms not_conjecture
#print axioms not_realConjecture
#print axioms exists_gcdClosed_singular_lcmMatrix

end BourqueLigh
