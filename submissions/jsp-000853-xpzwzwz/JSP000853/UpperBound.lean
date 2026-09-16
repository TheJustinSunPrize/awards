import JSP000853.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The grid construction

The explicit construction used for the upper-bound half of Erdős Problem #1025.
Vertices are points of a square grid.  For two points in different rows and
columns, the pair maps to the opposite corner whose first coordinate comes from
the left point.  Degenerate pairs use the canonical fallback point.
-/

namespace JSP000853

abbrev Grid (n : ℕ) := Fin n × Fin n

noncomputable instance gridLinearOrder (n : ℕ) : LinearOrder (Grid n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

noncomputable def gridCore {n : ℕ} (hcard : 2 < Fintype.card (Grid n))
    (p q : Grid n) : Grid n :=
  if _hdeg : p.1 = q.1 ∨ p.2 = q.2 then
    fallbackPoint hcard p q
  else if p.1 < q.1 then
    (p.1, q.2)
  else
    (q.1, p.2)

theorem gridCore_comm {n : ℕ} (hcard : 2 < Fintype.card (Grid n))
    (p q : Grid n) : gridCore hcard p q = gridCore hcard q p := by
  classical
  unfold gridCore
  by_cases hdeg : p.1 = q.1 ∨ p.2 = q.2
  · have hdeg' : q.1 = p.1 ∨ q.2 = p.2 := hdeg.imp Eq.symm Eq.symm
    simp only [hdeg, hdeg', dite_true]
    exact fallbackPoint_comm hcard p q
  · have hdeg' : ¬(q.1 = p.1 ∨ q.2 = p.2) := by
      intro h
      exact hdeg (h.imp Eq.symm Eq.symm)
    simp only [hdeg, hdeg', dite_false]
    have hx : p.1 ≠ q.1 := fun h => hdeg (Or.inl h)
    by_cases hpq : p.1 < q.1
    · have hqp : ¬q.1 < p.1 := not_lt_of_ge (le_of_lt hpq)
      simp only [hpq, hqp, ite_true, ite_false]
    · have hqp : q.1 < p.1 := lt_of_le_of_ne (le_of_not_gt hpq) hx.symm
      simp only [hpq, hqp, ite_true, ite_false]

theorem gridCore_ne_left {n : ℕ} (hcard : 2 < Fintype.card (Grid n))
    {p q : Grid n} (_hpq : p ≠ q) : gridCore hcard p q ≠ p := by
  classical
  unfold gridCore
  by_cases hdeg : p.1 = q.1 ∨ p.2 = q.2
  · simp only [hdeg, dite_true]
    exact fallbackPoint_ne_left hcard p q
  · simp only [hdeg, dite_false]
    have hx : p.1 ≠ q.1 := fun h => hdeg (Or.inl h)
    have hy : p.2 ≠ q.2 := fun h => hdeg (Or.inr h)
    by_cases hlt : p.1 < q.1
    · simp only [hlt, ite_true]
      intro h
      exact hy (congrArg Prod.snd h).symm
    · simp only [hlt, ite_false]
      intro h
      exact hx (congrArg Prod.fst h).symm

theorem gridCore_ne_right {n : ℕ} (hcard : 2 < Fintype.card (Grid n))
    {p q : Grid n} (hpq : p ≠ q) : gridCore hcard p q ≠ q := by
  rw [gridCore_comm hcard p q]
  exact gridCore_ne_left hcard hpq.symm

/-- The admissible mapping underlying the Conlon--Fox--Sudakov grid construction. -/
noncomputable def gridMapping {n : ℕ} (hcard : 2 < Fintype.card (Grid n)) :
    PairMapping (Grid n) where
  toFun := gridCore hcard
  map_symm := gridCore_comm hcard
  map_ne_left := gridCore_ne_left hcard
  map_ne_right := gridCore_ne_right hcard

end JSP000853
