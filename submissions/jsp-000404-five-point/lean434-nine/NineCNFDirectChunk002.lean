import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause2639 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2649 (t x03 x06 x36 : ℝ) : (((t + x06 + ((-1) * x36)) ≥ 1) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x06 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2702 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x03 ≤ x06) ∨ (x36 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2703 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x03 ≤ x06) ∨ (x06 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2704 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x03 ≤ x06) ∨ ((x03 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2705 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x03 ≤ x06) ∨ ((x03 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2706 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x03 ≤ x06) ∨ ((x06 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2707 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x06 ≤ x36) ∨ (x36 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2708 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x06 ≤ x36) ∨ (x06 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2709 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x06 ≤ x36) ∨ ((x03 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2710 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x06 ≤ x36) ∨ ((x03 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2711 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : ((x06 ≤ x36) ∨ ((x06 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2712 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x03) ≥ 1) ∨ (x36 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2713 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x03) ≥ 1) ∨ (x06 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2714 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x03) ≥ 1) ∨ ((x03 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2715 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x03) ≥ 1) ∨ ((x03 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2716 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x03) ≥ 1) ∨ ((x06 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2717 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x06 - x03) ≤ (t - 1)) ∨ (x36 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2718 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x06 - x03) ≤ (t - 1)) ∨ (x06 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2719 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x06 - x03) ≤ (t - 1)) ∨ ((x03 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2720 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x06 - x03) ≤ (t - 1)) ∨ ((x03 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2721 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x06 - x03) ≤ (t - 1)) ∨ ((x06 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2722 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x06) ≤ (t - 1)) ∨ (x36 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2723 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x06) ≤ (t - 1)) ∨ (x06 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2724 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x06) ≤ (t - 1)) ∨ ((x03 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2725 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x06) ≤ (t - 1)) ∨ ((x03 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2726 (t x03 x06 x36 : ℝ) (h : (((x03 ≤ x06) ∧ (x06 ≤ x36) ∧ ((x36 - x03) ≥ 1) ∧ ((x06 - x03) ≤ (t - 1)) ∧ ((x36 - x06) ≤ (t - 1))) ∨ ((x36 ≤ x06) ∧ (x06 ≤ x03) ∧ ((x03 - x36) ≥ 1) ∧ ((x03 - x06) ≤ (t - 1)) ∧ ((x06 - x36) ≤ (t - 1))))) : (((x36 - x06) ≤ (t - 1)) ∨ ((x06 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2727 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≥ 0) ∨ ((x01 + ((-1) * x04)) ≤ 0) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2730 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x04)) ≤ 0) ∨ ((t + ((-1) * x01) + x04) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2734 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≤ 0) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2736 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≤ 0) ∨ ((t + ((-1) * x04) + x14) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2737 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≥ 0) ∨ ((x01 + ((-1) * x14)) ≤ (-1)) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2738 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((x01 + ((-1) * x04)) ≥ 0) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2739 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2740 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x04) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2744 (t x01 x04 x14 : ℝ) : (((t + x01 + ((-1) * x04)) ≥ 1) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x01 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2749 (t x01 x04 x14 : ℝ) : (((t + x04 + ((-1) * x14)) ≥ 1) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x01 ≤ x04)) ∨ (¬ (x04 ≤ x14)) ∨ (¬ ((x14 - x01) ≥ 1)) ∨ (¬ ((x04 - x01) ≤ (t - 1))) ∨ (¬ ((x14 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x04 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2752 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≥ 0) ∨ ((x01 + ((-1) * x04)) ≤ 0) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2754 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x04)) ≤ 0) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2755 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x04)) ≤ 0) ∨ ((t + ((-1) * x01) + x04) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2758 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≤ 0) ∨ ((x01 + ((-1) * x04)) ≥ 0) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2759 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≤ 0) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2761 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≤ 0) ∨ ((t + ((-1) * x04) + x14) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2762 (t x01 x04 x14 : ℝ) : (((x04 + ((-1) * x14)) ≥ 0) ∨ ((x01 + ((-1) * x14)) ≤ (-1)) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2763 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((x01 + ((-1) * x04)) ≥ 0) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2764 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2765 (t x01 x04 x14 : ℝ) : (((x01 + ((-1) * x14)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x04) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x14)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2769 (t x01 x04 x14 : ℝ) : (((t + x01 + ((-1) * x04)) ≥ 1) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x01 + ((-1) * x04)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2774 (t x01 x04 x14 : ℝ) : (((t + x04 + ((-1) * x14)) ≥ 1) ∨ ((x01 + ((-1) * x14)) ≥ 1) ∨ (¬ (x14 ≤ x04)) ∨ (¬ (x04 ≤ x01)) ∨ (¬ ((x01 - x14) ≥ 1)) ∨ (¬ ((x01 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x04 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th157 t x01 x04 x14
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2827 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x01 ≤ x04) ∨ (x14 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2828 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x01 ≤ x04) ∨ (x04 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2829 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x01 ≤ x04) ∨ ((x01 - x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x14) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2830 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x01 ≤ x04) ∨ ((x01 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2831 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x01 ≤ x04) ∨ ((x04 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2832 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x04 ≤ x14) ∨ (x14 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2833 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x04 ≤ x14) ∨ (x04 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2834 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x04 ≤ x14) ∨ ((x01 - x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x14) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2835 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x04 ≤ x14) ∨ ((x01 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2836 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : ((x04 ≤ x14) ∨ ((x04 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2837 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x01) ≥ 1) ∨ (x14 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2838 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x01) ≥ 1) ∨ (x04 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2839 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x01) ≥ 1) ∨ ((x01 - x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x14) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2840 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x01) ≥ 1) ∨ ((x01 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2841 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x01) ≥ 1) ∨ ((x04 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2842 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x04 - x01) ≤ (t - 1)) ∨ (x14 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2843 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x04 - x01) ≤ (t - 1)) ∨ (x04 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2844 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x04 - x01) ≤ (t - 1)) ∨ ((x01 - x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x14) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2845 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x04 - x01) ≤ (t - 1)) ∨ ((x01 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2846 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x04 - x01) ≤ (t - 1)) ∨ ((x04 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2847 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x04) ≤ (t - 1)) ∨ (x14 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2848 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x04) ≤ (t - 1)) ∨ (x04 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2849 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x04) ≤ (t - 1)) ∨ ((x01 - x14) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x14) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2850 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x04) ≤ (t - 1)) ∨ ((x01 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2851 (t x01 x04 x14 : ℝ) (h : (((x01 ≤ x04) ∧ (x04 ≤ x14) ∧ ((x14 - x01) ≥ 1) ∧ ((x04 - x01) ≤ (t - 1)) ∧ ((x14 - x04) ≤ (t - 1))) ∨ ((x14 ≤ x04) ∧ (x04 ≤ x01) ∧ ((x01 - x14) ≥ 1) ∧ ((x01 - x04) ≤ (t - 1)) ∧ ((x04 - x14) ≤ (t - 1))))) : (((x14 - x04) ≤ (t - 1)) ∨ ((x04 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2852 (t x24 x34 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th159 t x24 x34 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 (And.intro u1 u4))))))) h

theorem clause2853 (t x23 x24 x34 : ℝ) : ((¬ (x23 ≥ 0)) ∨ ((t + ((-1) * x24)) ≤ 0) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x24) + x34) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x24) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th160 t x23 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 u3))))) h

theorem clause2854 (t x24 : ℝ) : ((¬ ((t + ((-1) * x24)) ≤ 0)) ∨ (t ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x24) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th161 t x24
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2856 (t x24 : ℝ) : ((¬ (t ≤ x24)) ∨ (¬ (x24 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x24 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th162 t x24
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2858 (t x24 : ℝ) (h : (x24 < t)) : ((x24 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 < t) := fun hh => hn hh
  exact u0 h

theorem clause2861 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x24 + ((-1) * x26)) ≤ 0) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2865 (t x24 x26 x46 : ℝ) : (((x26 + ((-1) * x46)) ≤ 0) ∨ ((x24 + ((-1) * x26)) ≥ 0) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2866 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x26 + ((-1) * x46)) ≤ 0) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2868 (t x24 x26 x46 : ℝ) : (((x26 + ((-1) * x46)) ≤ 0) ∨ ((t + ((-1) * x26) + x46) ≥ 1) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2869 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((x26 + ((-1) * x46)) ≥ 0) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2870 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((x24 + ((-1) * x26)) ≥ 0) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2871 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x24 + ((-1) * x46)) ≤ (-1)) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2872 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x24) + x26) ≥ 1) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2873 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x26) + x46) ≥ 1) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2876 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((t + x24 + ((-1) * x26)) ≥ 1) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x24 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2881 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((t + x26 + ((-1) * x46)) ≥ 1) ∨ (¬ (x24 ≤ x26)) ∨ (¬ (x26 ≤ x46)) ∨ (¬ ((x46 - x24) ≥ 1)) ∨ (¬ ((x26 - x24) ≤ (t - 1))) ∨ (¬ ((x46 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x26 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2886 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x24 + ((-1) * x26)) ≤ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2890 (t x24 x26 x46 : ℝ) : (((x26 + ((-1) * x46)) ≤ 0) ∨ ((x24 + ((-1) * x26)) ≥ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2891 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x26 + ((-1) * x46)) ≤ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2894 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((x26 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2895 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((x24 + ((-1) * x26)) ≥ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2896 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((x24 + ((-1) * x46)) ≤ (-1)) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2897 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x24) + x26) ≥ 1) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2898 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x26) + x46) ≥ 1) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2901 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((t + x24 + ((-1) * x26)) ≥ 1) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x24 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2904 (t x24 x26 x46 : ℝ) : (((t + x26 + ((-1) * x46)) ≥ 1) ∨ ((x26 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x26 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2906 (t x24 x26 x46 : ℝ) : (((x24 + ((-1) * x46)) ≥ 1) ∨ ((t + x26 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x26)) ∨ (¬ (x26 ≤ x24)) ∨ (¬ ((x24 - x46) ≥ 1)) ∨ (¬ ((x24 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x26 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th165 t x24 x26 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2959 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x24 ≤ x26) ∨ (x46 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2960 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x24 ≤ x26) ∨ (x26 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2961 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x24 ≤ x26) ∨ ((x24 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2962 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x24 ≤ x26) ∨ ((x24 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2963 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x24 ≤ x26) ∨ ((x26 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2964 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x26 ≤ x46) ∨ (x46 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2965 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x26 ≤ x46) ∨ (x26 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2966 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x26 ≤ x46) ∨ ((x24 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2967 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x26 ≤ x46) ∨ ((x24 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2968 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : ((x26 ≤ x46) ∨ ((x26 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2969 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x24) ≥ 1) ∨ (x46 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2970 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x24) ≥ 1) ∨ (x26 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2971 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x24) ≥ 1) ∨ ((x24 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2972 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x24) ≥ 1) ∨ ((x24 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2973 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x24) ≥ 1) ∨ ((x26 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2974 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x26 - x24) ≤ (t - 1)) ∨ (x46 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2975 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x26 - x24) ≤ (t - 1)) ∨ (x26 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2976 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x26 - x24) ≤ (t - 1)) ∨ ((x24 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2977 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x26 - x24) ≤ (t - 1)) ∨ ((x24 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2978 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x26 - x24) ≤ (t - 1)) ∨ ((x26 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2979 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x26) ≤ (t - 1)) ∨ (x46 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2980 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x26) ≤ (t - 1)) ∨ (x26 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2981 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x26) ≤ (t - 1)) ∨ ((x24 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2982 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x26) ≤ (t - 1)) ∨ ((x24 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2983 (t x24 x26 x46 : ℝ) (h : (((x24 ≤ x26) ∧ (x26 ≤ x46) ∧ ((x46 - x24) ≥ 1) ∧ ((x26 - x24) ≤ (t - 1)) ∧ ((x46 - x26) ≤ (t - 1))) ∨ ((x46 ≤ x26) ∧ (x26 ≤ x24) ∧ ((x24 - x46) ≥ 1) ∧ ((x24 - x26) ≤ (t - 1)) ∧ ((x26 - x46) ≤ (t - 1))))) : (((x46 - x26) ≤ (t - 1)) ∨ ((x26 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2984 (t x01 x03 x14 x35 x47 x58 x78 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x78)) ≤ (-1))) ∨ (¬ ((t + x58 + ((-1) * x78)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + x01 + ((-1) * x03)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x14 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 + ((-1) * x78)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x58 + ((-1) * x78)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th167 t x01 x03 x14 x35 x47 x58 x78
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u2 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u3 (And.intro u4 u7))))))))) h

theorem clause2985 (x05 : ℝ) (h : (x05 ≥ 0)) : ((x05 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause2989 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≤ 0) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2990 (t x35 x36 x56 : ℝ) : (((t + ((-1) * x35) + x36) ≥ 1) ∨ ((x35 + ((-1) * x36)) ≤ 0) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x35) + x36) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2993 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≥ 0) ∨ ((x36 + ((-1) * x56)) ≤ 0) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2994 (t x35 x36 x56 : ℝ) : (((x36 + ((-1) * x56)) ≤ 0) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2997 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((x36 + ((-1) * x56)) ≥ 0) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2998 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≥ 0) ∨ ((x35 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2999 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3000 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x35) + x36) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3001 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x36) + x56) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3003 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≥ 0) ∨ ((t + x35 + ((-1) * x36)) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x35 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3007 (t x35 x36 x56 : ℝ) : (((t + x36 + ((-1) * x56)) ≥ 1) ∨ ((x36 + ((-1) * x56)) ≥ 0) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3009 (t x35 x36 x56 : ℝ) : (((t + x36 + ((-1) * x56)) ≥ 1) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x35 ≤ x36)) ∨ (¬ (x36 ≤ x56)) ∨ (¬ ((x56 - x35) ≥ 1)) ∨ (¬ ((x36 - x35) ≤ (t - 1))) ∨ (¬ ((x56 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3014 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≤ 0) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3019 (t x35 x36 x56 : ℝ) : (((x36 + ((-1) * x56)) ≤ 0) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3021 (t x35 x36 x56 : ℝ) : (((x36 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x36) + x56) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3022 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((x36 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3023 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≥ 0) ∨ ((x35 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3024 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3025 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x35) + x36) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x35) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3026 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x36) + x56) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3028 (t x35 x36 x56 : ℝ) : (((x35 + ((-1) * x36)) ≥ 0) ∨ ((t + x35 + ((-1) * x36)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x35 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3029 (t x35 x36 x56 : ℝ) : (((t + x35 + ((-1) * x36)) ≥ 1) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x35 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3032 (t x35 x36 x56 : ℝ) : (((t + x36 + ((-1) * x56)) ≥ 1) ∨ ((x36 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3034 (t x35 x36 x56 : ℝ) : (((t + x36 + ((-1) * x56)) ≥ 1) ∨ ((x35 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x36)) ∨ (¬ (x36 ≤ x35)) ∨ (¬ ((x35 - x56) ≥ 1)) ∨ (¬ ((x35 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th174 t x35 x36 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3087 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x35 ≤ x36) ∨ (x56 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3088 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x35 ≤ x36) ∨ (x36 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3089 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x35 ≤ x36) ∨ ((x35 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3090 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x35 ≤ x36) ∨ ((x35 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3091 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x35 ≤ x36) ∨ ((x36 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3092 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x36 ≤ x56) ∨ (x56 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3093 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x36 ≤ x56) ∨ (x36 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3094 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x36 ≤ x56) ∨ ((x35 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3095 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x36 ≤ x56) ∨ ((x35 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3096 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : ((x36 ≤ x56) ∨ ((x36 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3097 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x35) ≥ 1) ∨ (x56 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3098 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x35) ≥ 1) ∨ (x36 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3099 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x35) ≥ 1) ∨ ((x35 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3100 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x35) ≥ 1) ∨ ((x35 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3101 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x35) ≥ 1) ∨ ((x36 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x35) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3102 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x36 - x35) ≤ (t - 1)) ∨ (x56 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3103 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x36 - x35) ≤ (t - 1)) ∨ (x36 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3104 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x36 - x35) ≤ (t - 1)) ∨ ((x35 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3105 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x36 - x35) ≤ (t - 1)) ∨ ((x35 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3106 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x36 - x35) ≤ (t - 1)) ∨ ((x36 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x35) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3107 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x36) ≤ (t - 1)) ∨ (x56 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3108 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x36) ≤ (t - 1)) ∨ (x36 ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x35) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3109 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x36) ≤ (t - 1)) ∨ ((x35 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3110 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x36) ≤ (t - 1)) ∨ ((x35 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x35 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3111 (t x35 x36 x56 : ℝ) (h : (((x35 ≤ x36) ∧ (x36 ≤ x56) ∧ ((x56 - x35) ≥ 1) ∧ ((x36 - x35) ≤ (t - 1)) ∧ ((x56 - x36) ≤ (t - 1))) ∨ ((x56 ≤ x36) ∧ (x36 ≤ x35) ∧ ((x35 - x56) ≥ 1) ∧ ((x35 - x36) ≤ (t - 1)) ∧ ((x36 - x56) ≤ (t - 1))))) : (((x56 - x36) ≤ (t - 1)) ∨ ((x36 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3114 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x03 + ((-1) * x05)) ≤ 0) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3119 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x05 + ((-1) * x35)) ≤ 0) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3122 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((x05 + ((-1) * x35)) ≥ 0) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3123 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((x03 + ((-1) * x05)) ≥ 0) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3124 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x03 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3126 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x05) + x35) ≥ 1) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3134 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((t + x05 + ((-1) * x35)) ≥ 1) ∨ (¬ (x03 ≤ x05)) ∨ (¬ (x05 ≤ x35)) ∨ (¬ ((x35 - x03) ≥ 1)) ∨ (¬ ((x05 - x03) ≤ (t - 1))) ∨ (¬ ((x35 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x05 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3137 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x05)) ≤ 0) ∨ ((x05 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3139 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x03 + ((-1) * x05)) ≤ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3144 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x05 + ((-1) * x35)) ≤ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3147 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((x05 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3148 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((x03 + ((-1) * x05)) ≥ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3149 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≥ 1) ∨ ((x03 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3151 (t x03 x05 x35 : ℝ) : (((x03 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x05) + x35) ≥ 1) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3157 (t x03 x05 x35 : ℝ) : (((t + x05 + ((-1) * x35)) ≥ 1) ∨ ((x05 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x05)) ∨ (¬ (x05 ≤ x03)) ∨ (¬ ((x03 - x35) ≥ 1)) ∨ (¬ ((x03 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x05 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th177 t x03 x05 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3212 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x03 ≤ x05) ∨ (x35 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3213 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x03 ≤ x05) ∨ (x05 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3214 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x03 ≤ x05) ∨ ((x03 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3215 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x03 ≤ x05) ∨ ((x03 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3216 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x03 ≤ x05) ∨ ((x05 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3217 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x05 ≤ x35) ∨ (x35 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3218 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x05 ≤ x35) ∨ (x05 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3219 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x05 ≤ x35) ∨ ((x03 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3220 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x05 ≤ x35) ∨ ((x03 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3221 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : ((x05 ≤ x35) ∨ ((x05 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3222 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x03) ≥ 1) ∨ (x35 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3223 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x03) ≥ 1) ∨ (x05 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3224 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x03) ≥ 1) ∨ ((x03 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3225 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x03) ≥ 1) ∨ ((x03 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3226 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x03) ≥ 1) ∨ ((x05 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3227 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x05 - x03) ≤ (t - 1)) ∨ (x35 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3228 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x05 - x03) ≤ (t - 1)) ∨ (x05 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3229 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x05 - x03) ≤ (t - 1)) ∨ ((x03 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3230 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x05 - x03) ≤ (t - 1)) ∨ ((x03 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3231 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x05 - x03) ≤ (t - 1)) ∨ ((x05 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3232 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x05) ≤ (t - 1)) ∨ (x35 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3233 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x05) ≤ (t - 1)) ∨ (x05 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3234 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x05) ≤ (t - 1)) ∨ ((x03 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3235 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x05) ≤ (t - 1)) ∨ ((x03 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3236 (t x03 x05 x35 : ℝ) (h : (((x03 ≤ x05) ∧ (x05 ≤ x35) ∧ ((x35 - x03) ≥ 1) ∧ ((x05 - x03) ≤ (t - 1)) ∧ ((x35 - x05) ≤ (t - 1))) ∨ ((x35 ≤ x05) ∧ (x05 ≤ x03) ∧ ((x03 - x35) ≥ 1) ∧ ((x03 - x05) ≤ (t - 1)) ∧ ((x05 - x35) ≤ (t - 1))))) : (((x35 - x05) ≤ (t - 1)) ∨ ((x05 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3237 (x04 x14 x24 : ℝ) : ((¬ ((x04 + ((-1) * x24)) ≥ 0)) ∨ ((x04 + ((-1) * x14)) ≥ 0) ∨ (¬ ((x14 + ((-1) * x24)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th179 x04 x14 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause3240 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x14)) ≤ 0) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3244 (t x12 x14 x24 : ℝ) : (((x14 + ((-1) * x24)) ≤ 0) ∨ ((x12 + ((-1) * x14)) ≥ 0) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3245 (t x12 x14 x24 : ℝ) : (((x14 + ((-1) * x24)) ≤ 0) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3248 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x14 + ((-1) * x24)) ≥ 0) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3249 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x12 + ((-1) * x14)) ≥ 0) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3250 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3251 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x14) ≥ 1) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3254 (t x12 x14 x24 : ℝ) : (((t + x12 + ((-1) * x14)) ≥ 1) ∨ ((x12 + ((-1) * x14)) ≥ 0) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3255 (t x12 x14 x24 : ℝ) : (((t + x12 + ((-1) * x14)) ≥ 1) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x12 ≤ x14)) ∨ (¬ (x14 ≤ x24)) ∨ (¬ ((x24 - x12) ≥ 1)) ∨ (¬ ((x14 - x12) ≤ (t - 1))) ∨ (¬ ((x24 - x14) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3263 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x14)) ≤ 0) ∨ ((x14 + ((-1) * x24)) ≥ 0) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3265 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x14)) ≤ 0) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x14)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3269 (t x12 x14 x24 : ℝ) : (((x14 + ((-1) * x24)) ≤ 0) ∨ ((x12 + ((-1) * x14)) ≥ 0) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3270 (t x12 x14 x24 : ℝ) : (((x14 + ((-1) * x24)) ≤ 0) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3273 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x14 + ((-1) * x24)) ≥ 0) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3274 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x12 + ((-1) * x14)) ≥ 0) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x14)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3275 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3276 (t x12 x14 x24 : ℝ) : (((x12 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x14) ≥ 1) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x14) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3280 (t x12 x14 x24 : ℝ) : (((t + x12 + ((-1) * x14)) ≥ 1) ∨ ((x12 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x14)) ∨ (¬ (x14 ≤ x12)) ∨ (¬ ((x12 - x24) ≥ 1)) ∨ (¬ ((x12 - x14) ≤ (t - 1))) ∨ (¬ ((x14 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x14)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x14 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x14 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th181 t x12 x14 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3338 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x12 ≤ x14) ∨ (x24 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3339 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x12 ≤ x14) ∨ (x14 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3340 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x12 ≤ x14) ∨ ((x12 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3341 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x12 ≤ x14) ∨ ((x12 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3342 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x12 ≤ x14) ∨ ((x14 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x14) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3343 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x14 ≤ x24) ∨ (x24 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3344 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x14 ≤ x24) ∨ (x14 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3345 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x14 ≤ x24) ∨ ((x12 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3346 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x14 ≤ x24) ∨ ((x12 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3347 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : ((x14 ≤ x24) ∨ ((x14 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3348 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x12) ≥ 1) ∨ (x24 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3349 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x12) ≥ 1) ∨ (x14 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3350 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x12) ≥ 1) ∨ ((x12 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3351 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x12) ≥ 1) ∨ ((x12 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3352 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x12) ≥ 1) ∨ ((x14 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3353 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x14 - x12) ≤ (t - 1)) ∨ (x24 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3354 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x14 - x12) ≤ (t - 1)) ∨ (x14 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3355 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x14 - x12) ≤ (t - 1)) ∨ ((x12 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3356 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x14 - x12) ≤ (t - 1)) ∨ ((x12 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3357 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x14 - x12) ≤ (t - 1)) ∨ ((x14 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3358 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x14) ≤ (t - 1)) ∨ (x24 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3359 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x14) ≤ (t - 1)) ∨ (x14 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x14 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3360 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x14) ≤ (t - 1)) ∨ ((x12 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3361 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x14) ≤ (t - 1)) ∨ ((x12 - x14) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x14) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3362 (t x12 x14 x24 : ℝ) (h : (((x12 ≤ x14) ∧ (x14 ≤ x24) ∧ ((x24 - x12) ≥ 1) ∧ ((x14 - x12) ≤ (t - 1)) ∧ ((x24 - x14) ≤ (t - 1))) ∨ ((x24 ≤ x14) ∧ (x14 ≤ x12) ∧ ((x12 - x24) ≥ 1) ∧ ((x12 - x14) ≤ (t - 1)) ∧ ((x14 - x24) ≤ (t - 1))))) : (((x24 - x14) ≤ (t - 1)) ∨ ((x14 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3363 (x01 x14 x16 : ℝ) : ((¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x16)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th183 x01 x14 x16
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause3364 (t x01 x14 x16 x24 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x14) + x24) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x16)) ≥ 1)) ∨ (¬ ((x16 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x14) + x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x16)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th184 t x01 x14 x16 x24 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause3365 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x16)) ≤ 0) ∨ ((x16 + ((-1) * x46)) ≥ 0) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3367 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x16)) ≤ 0) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3372 (t x14 x16 x46 : ℝ) : (((x16 + ((-1) * x46)) ≤ 0) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3375 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x16 + ((-1) * x46)) ≥ 0) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3376 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x14 + ((-1) * x16)) ≥ 0) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3377 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3379 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x46) ≥ 1) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3381 (t x14 x16 x46 : ℝ) : (((t + x14 + ((-1) * x16)) ≥ 1) ∨ ((x14 + ((-1) * x16)) ≥ 0) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x14 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3385 (t x14 x16 x46 : ℝ) : (((x16 + ((-1) * x46)) ≥ 0) ∨ ((t + x16 + ((-1) * x46)) ≥ 1) ∨ (¬ (x14 ≤ x16)) ∨ (¬ (x16 ≤ x46)) ∨ (¬ ((x46 - x14) ≥ 1)) ∨ (¬ ((x16 - x14) ≤ (t - 1))) ∨ (¬ ((x46 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x16 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3390 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x16)) ≤ 0) ∨ ((x16 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3392 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x16)) ≤ 0) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3396 (t x14 x16 x46 : ℝ) : (((x16 + ((-1) * x46)) ≤ 0) ∨ ((x14 + ((-1) * x16)) ≥ 0) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3397 (t x14 x16 x46 : ℝ) : (((x16 + ((-1) * x46)) ≤ 0) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3400 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x16 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3401 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x14 + ((-1) * x16)) ≥ 0) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3402 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3404 (t x14 x16 x46 : ℝ) : (((x14 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x46) ≥ 1) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3406 (t x14 x16 x46 : ℝ) : (((t + x14 + ((-1) * x16)) ≥ 1) ∨ ((x14 + ((-1) * x16)) ≥ 0) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x14 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3412 (t x14 x16 x46 : ℝ) : (((t + x16 + ((-1) * x46)) ≥ 1) ∨ ((x14 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x16)) ∨ (¬ (x16 ≤ x14)) ∨ (¬ ((x14 - x46) ≥ 1)) ∨ (¬ ((x14 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x16 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th186 t x14 x16 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3465 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x14 ≤ x16) ∨ (x46 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3466 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x14 ≤ x16) ∨ (x16 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3467 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x14 ≤ x16) ∨ ((x14 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3468 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x14 ≤ x16) ∨ ((x14 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3469 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x14 ≤ x16) ∨ ((x16 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3470 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x16 ≤ x46) ∨ (x46 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3471 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x16 ≤ x46) ∨ (x16 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3472 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x16 ≤ x46) ∨ ((x14 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3473 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x16 ≤ x46) ∨ ((x14 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3474 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : ((x16 ≤ x46) ∨ ((x16 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3475 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x14) ≥ 1) ∨ (x46 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3476 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x14) ≥ 1) ∨ (x16 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3477 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x14) ≥ 1) ∨ ((x14 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3478 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x14) ≥ 1) ∨ ((x14 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3479 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x14) ≥ 1) ∨ ((x16 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3480 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x16 - x14) ≤ (t - 1)) ∨ (x46 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3481 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x16 - x14) ≤ (t - 1)) ∨ (x16 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3482 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x16 - x14) ≤ (t - 1)) ∨ ((x14 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3483 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x16 - x14) ≤ (t - 1)) ∨ ((x14 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3484 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x16 - x14) ≤ (t - 1)) ∨ ((x16 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3485 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x16) ≤ (t - 1)) ∨ (x46 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3486 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x16) ≤ (t - 1)) ∨ (x16 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3487 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x16) ≤ (t - 1)) ∨ ((x14 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3488 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x16) ≤ (t - 1)) ∨ ((x14 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3489 (t x14 x16 x46 : ℝ) (h : (((x14 ≤ x16) ∧ (x16 ≤ x46) ∧ ((x46 - x14) ≥ 1) ∧ ((x16 - x14) ≤ (t - 1)) ∧ ((x46 - x16) ≤ (t - 1))) ∨ ((x46 ≤ x16) ∧ (x16 ≤ x14) ∧ ((x14 - x46) ≥ 1) ∧ ((x14 - x16) ≤ (t - 1)) ∧ ((x16 - x46) ≤ (t - 1))))) : (((x46 - x16) ≤ (t - 1)) ∨ ((x16 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3492 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x01 + ((-1) * x06)) ≤ 0) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3493 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x06)) ≤ 0) ∨ ((t + ((-1) * x01) + x06) ≥ 1) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3497 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x06 + ((-1) * x16)) ≤ 0) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3500 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((x06 + ((-1) * x16)) ≥ 0) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3501 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((x01 + ((-1) * x06)) ≥ 0) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3502 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x01 + ((-1) * x16)) ≤ (-1)) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3504 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x16) ≥ 1) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3506 (t x01 x06 x16 : ℝ) : (((t + x01 + ((-1) * x06)) ≥ 1) ∨ ((x01 + ((-1) * x06)) ≥ 0) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x01 + ((-1) * x06)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3507 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((t + x01 + ((-1) * x06)) ≥ 1) ∨ (¬ (x01 ≤ x06)) ∨ (¬ (x06 ≤ x16)) ∨ (¬ ((x16 - x01) ≥ 1)) ∨ (¬ ((x06 - x01) ≤ (t - 1))) ∨ (¬ ((x16 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x06)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3517 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x01 + ((-1) * x06)) ≤ 0) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3518 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x06)) ≤ 0) ∨ ((t + ((-1) * x01) + x06) ≥ 1) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3522 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x06 + ((-1) * x16)) ≤ 0) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3525 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((x06 + ((-1) * x16)) ≥ 0) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3526 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((x01 + ((-1) * x06)) ≥ 0) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3527 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((x01 + ((-1) * x16)) ≤ (-1)) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3529 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x16) ≥ 1) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3532 (t x01 x06 x16 : ℝ) : (((x01 + ((-1) * x16)) ≥ 1) ∨ ((t + x01 + ((-1) * x06)) ≥ 1) ∨ (¬ (x16 ≤ x06)) ∨ (¬ (x06 ≤ x01)) ∨ (¬ ((x01 - x16) ≥ 1)) ∨ (¬ ((x01 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x06)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th189 t x01 x06 x16
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3590 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x01 ≤ x06) ∨ (x16 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3591 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x01 ≤ x06) ∨ (x06 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3592 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x01 ≤ x06) ∨ ((x01 - x16) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x16) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3593 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x01 ≤ x06) ∨ ((x01 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3594 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x01 ≤ x06) ∨ ((x06 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3595 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x06 ≤ x16) ∨ (x16 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3596 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x06 ≤ x16) ∨ (x06 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3597 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x06 ≤ x16) ∨ ((x01 - x16) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x16) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3598 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x06 ≤ x16) ∨ ((x01 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3599 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : ((x06 ≤ x16) ∨ ((x06 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3600 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x01) ≥ 1) ∨ (x16 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3601 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x01) ≥ 1) ∨ (x06 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3602 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x01) ≥ 1) ∨ ((x01 - x16) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x16) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3603 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x01) ≥ 1) ∨ ((x01 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3604 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x01) ≥ 1) ∨ ((x06 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3605 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x06 - x01) ≤ (t - 1)) ∨ (x16 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3606 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x06 - x01) ≤ (t - 1)) ∨ (x06 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3607 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x06 - x01) ≤ (t - 1)) ∨ ((x01 - x16) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x16) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3608 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x06 - x01) ≤ (t - 1)) ∨ ((x01 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3609 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x06 - x01) ≤ (t - 1)) ∨ ((x06 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3610 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x06) ≤ (t - 1)) ∨ (x16 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3611 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x06) ≤ (t - 1)) ∨ (x06 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3612 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x06) ≤ (t - 1)) ∨ ((x01 - x16) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x16) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3613 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x06) ≤ (t - 1)) ∨ ((x01 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3614 (t x01 x06 x16 : ℝ) (h : (((x01 ≤ x06) ∧ (x06 ≤ x16) ∧ ((x16 - x01) ≥ 1) ∧ ((x06 - x01) ≤ (t - 1)) ∧ ((x16 - x06) ≤ (t - 1))) ∨ ((x16 ≤ x06) ∧ (x06 ≤ x01) ∧ ((x01 - x16) ≥ 1) ∧ ((x01 - x06) ≤ (t - 1)) ∧ ((x06 - x16) ≤ (t - 1))))) : (((x16 - x06) ≤ (t - 1)) ∨ ((x06 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3615 (t x01 x04 x06 x14 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x04)) ≤ 0)) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x01 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x14 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th191 t x01 x04 x06 x14 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u6 (And.intro u8 u1)))))))))) h

theorem clause3616 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x45)) ≥ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3618 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x14 + ((-1) * x15)) ≤ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3623 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x15 + ((-1) * x45)) ≤ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3625 (t x14 x15 x45 : ℝ) : (((x15 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x15) + x45) ≥ 1) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x15) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3626 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((x15 + ((-1) * x45)) ≥ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3627 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((x14 + ((-1) * x15)) ≥ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3628 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x14 + ((-1) * x45)) ≤ (-1)) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3629 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x14) + x15) ≥ 1) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x14) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3632 (t x14 x15 x45 : ℝ) : (((t + x14 + ((-1) * x15)) ≥ 1) ∨ ((x14 + ((-1) * x15)) ≥ 0) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x14 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3633 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((t + x14 + ((-1) * x15)) ≥ 1) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x14 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3638 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((t + x15 + ((-1) * x45)) ≥ 1) ∨ (¬ (x14 ≤ x15)) ∨ (¬ (x15 ≤ x45)) ∨ (¬ ((x45 - x14) ≥ 1)) ∨ (¬ ((x15 - x14) ≤ (t - 1))) ∨ (¬ ((x45 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x15 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3641 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3643 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x14 + ((-1) * x15)) ≤ 0) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3648 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x15 + ((-1) * x45)) ≤ 0) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3650 (t x14 x15 x45 : ℝ) : (((x15 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x15) + x45) ≥ 1) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x15) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3651 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((x15 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3652 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((x14 + ((-1) * x15)) ≥ 0) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3653 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((x14 + ((-1) * x45)) ≤ (-1)) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3654 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x14) + x15) ≥ 1) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x14) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3658 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((t + x14 + ((-1) * x15)) ≥ 1) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x14 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3663 (t x14 x15 x45 : ℝ) : (((x14 + ((-1) * x45)) ≥ 1) ∨ ((t + x15 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x15)) ∨ (¬ (x15 ≤ x14)) ∨ (¬ ((x14 - x45) ≥ 1)) ∨ (¬ ((x14 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x15 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th193 t x14 x15 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3716 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x14 ≤ x15) ∨ (x45 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3717 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x14 ≤ x15) ∨ (x15 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3718 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x14 ≤ x15) ∨ ((x14 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3719 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x14 ≤ x15) ∨ ((x14 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3720 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x14 ≤ x15) ∨ ((x15 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3721 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x15 ≤ x45) ∨ (x45 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3722 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x15 ≤ x45) ∨ (x15 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3723 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x15 ≤ x45) ∨ ((x14 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3724 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x15 ≤ x45) ∨ ((x14 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3725 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : ((x15 ≤ x45) ∨ ((x15 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3726 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x14) ≥ 1) ∨ (x45 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3727 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x14) ≥ 1) ∨ (x15 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3728 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x14) ≥ 1) ∨ ((x14 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3729 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x14) ≥ 1) ∨ ((x14 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3730 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x14) ≥ 1) ∨ ((x15 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3731 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x15 - x14) ≤ (t - 1)) ∨ (x45 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3732 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x15 - x14) ≤ (t - 1)) ∨ (x15 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3733 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x15 - x14) ≤ (t - 1)) ∨ ((x14 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3734 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x15 - x14) ≤ (t - 1)) ∨ ((x14 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3735 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x15 - x14) ≤ (t - 1)) ∨ ((x15 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3736 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x15) ≤ (t - 1)) ∨ (x45 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3737 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x15) ≤ (t - 1)) ∨ (x15 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3738 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x15) ≤ (t - 1)) ∨ ((x14 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3739 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x15) ≤ (t - 1)) ∨ ((x14 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3740 (t x14 x15 x45 : ℝ) (h : (((x14 ≤ x15) ∧ (x15 ≤ x45) ∧ ((x45 - x14) ≥ 1) ∧ ((x15 - x14) ≤ (t - 1)) ∧ ((x45 - x15) ≤ (t - 1))) ∨ ((x45 ≤ x15) ∧ (x15 ≤ x14) ∧ ((x14 - x45) ≥ 1) ∧ ((x14 - x15) ≤ (t - 1)) ∧ ((x15 - x45) ≤ (t - 1))))) : (((x45 - x15) ≤ (t - 1)) ∨ ((x15 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3741 (t x01 x06 x14 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x36 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x01 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th195 t x01 x06 x14 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u5 (And.intro u2 (And.intro u4 (And.intro u3 (And.intro u1 u7))))))))) h

theorem clause3742 (t x35 x36 x56 : ℝ) : ((¬ (x36 ≥ 0)) ∨ ((t + x36 + ((-1) * x56)) ≥ 1) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x36 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x36 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th196 t x35 x36 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 u1))))) h

theorem clause3743 (t x35 : ℝ) : ((¬ ((t + ((-1) * x35)) ≤ 0)) ∨ (t ≤ x35)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x35) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th197 t x35
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3745 (t x35 : ℝ) : ((¬ (t ≤ x35)) ∨ (¬ (x35 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x35 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th198 t x35
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3747 (t x35 : ℝ) (h : (x35 < t)) : ((x35 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x35 < t) := fun hh => hn hh
  exact u0 h

theorem clause3748 (t x06 x35 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th200 t x06 x35 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 u1)))))))) h

theorem clause3749 (t x34 x35 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ ((t + x35 + ((-1) * x45)) ≥ 1) ∨ (¬ (x35 ≥ 0)) ∨ ((t + ((-1) * x34)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x35 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th201 t x34 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause3750 (t x05 x35 x36 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x35 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x35 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x35 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th202 t x05 x35 x36 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u6 (And.intro u0 u4)))))))) h

theorem clause3751 (x36 x56 x67 : ℝ) : ((¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x56 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th203 x36 x56 x67
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause3752 (t x03 x04 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ ((t + ((-1) * x04) + x34) ≥ 1) ∨ ((t + ((-1) * x04)) ≤ 0) ∨ (¬ (x03 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x34) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x03 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th205 t x03 x04 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause3753 (x03 : ℝ) (h : (x03 ≥ 0)) : ((x03 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause3754 (t x04 : ℝ) : ((¬ ((t + ((-1) * x04)) ≤ 0)) ∨ (t ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x04)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x04) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th207 t x04
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3756 (t x04 : ℝ) : ((¬ (t ≤ x04)) ∨ (¬ (x04 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x04 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th208 t x04
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3758 (t x04 : ℝ) (h : (x04 < t)) : ((x04 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 < t) := fun hh => hn hh
  exact u0 h

theorem clause3761 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((x56 + ((-1) * x57)) ≤ 0) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3766 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((x57 + ((-1) * x67)) ≤ 0) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3769 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x57 + ((-1) * x67)) ≥ 0) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3770 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x56 + ((-1) * x57)) ≥ 0) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3771 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x56 + ((-1) * x67)) ≥ 1) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3772 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x56) + x57) ≥ 1) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3773 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x57) + x67) ≥ 1) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x57) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3776 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((t + x56 + ((-1) * x57)) ≥ 1) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x56 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3781 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((t + x57 + ((-1) * x67)) ≥ 1) ∨ (¬ (x56 ≤ x57)) ∨ (¬ (x57 ≤ x67)) ∨ (¬ ((x67 - x56) ≥ 1)) ∨ (¬ ((x57 - x56) ≤ (t - 1))) ∨ (¬ ((x67 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x57 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x57 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3786 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((x56 + ((-1) * x57)) ≤ 0) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3791 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((x57 + ((-1) * x67)) ≤ 0) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3794 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x57 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3795 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x56 + ((-1) * x57)) ≥ 0) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3796 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((x56 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3797 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x56) + x57) ≥ 1) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3798 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x57) + x67) ≥ 1) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x57) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3801 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((t + x56 + ((-1) * x57)) ≥ 1) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x56 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3806 (t x56 x57 x67 : ℝ) : (((x56 + ((-1) * x67)) ≥ 1) ∨ ((t + x57 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x57)) ∨ (¬ (x57 ≤ x56)) ∨ (¬ ((x56 - x67) ≥ 1)) ∨ (¬ ((x56 - x57) ≤ (t - 1))) ∨ (¬ ((x57 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x57 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x57 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th211 t x56 x57 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3859 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x56 ≤ x57) ∨ (x67 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3860 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x56 ≤ x57) ∨ (x57 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3861 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x56 ≤ x57) ∨ ((x56 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3862 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x56 ≤ x57) ∨ ((x56 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3863 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x56 ≤ x57) ∨ ((x57 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3864 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x57 ≤ x67) ∨ (x67 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3865 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x57 ≤ x67) ∨ (x57 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3866 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x57 ≤ x67) ∨ ((x56 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3867 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x57 ≤ x67) ∨ ((x56 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3868 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : ((x57 ≤ x67) ∨ ((x57 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3869 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x56) ≥ 1) ∨ (x67 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3870 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x56) ≥ 1) ∨ (x57 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3871 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x56) ≥ 1) ∨ ((x56 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3872 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x56) ≥ 1) ∨ ((x56 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3873 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x56) ≥ 1) ∨ ((x57 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3874 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x57 - x56) ≤ (t - 1)) ∨ (x67 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3875 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x57 - x56) ≤ (t - 1)) ∨ (x57 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3876 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x57 - x56) ≤ (t - 1)) ∨ ((x56 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3877 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x57 - x56) ≤ (t - 1)) ∨ ((x56 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3878 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x57 - x56) ≤ (t - 1)) ∨ ((x57 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3879 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x57) ≤ (t - 1)) ∨ (x67 ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x57) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause3880 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x57) ≤ (t - 1)) ∨ (x57 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause3881 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x57) ≤ (t - 1)) ∨ ((x56 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause3882 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x57) ≤ (t - 1)) ∨ ((x56 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause3883 (t x56 x57 x67 : ℝ) (h : (((x56 ≤ x57) ∧ (x57 ≤ x67) ∧ ((x67 - x56) ≥ 1) ∧ ((x57 - x56) ≤ (t - 1)) ∧ ((x67 - x57) ≤ (t - 1))) ∨ ((x67 ≤ x57) ∧ (x57 ≤ x56) ∧ ((x56 - x67) ≥ 1) ∧ ((x56 - x57) ≤ (t - 1)) ∧ ((x57 - x67) ≤ (t - 1))))) : (((x67 - x57) ≤ (t - 1)) ∨ ((x57 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x57) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x57 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause3884 (t x05 x06 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x05) + x35) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x05) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th213 t x05 x06 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u4))))))) h

theorem clause3885 (t x05 x06 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x05) + x45) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x05) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th214 t x05 x06 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u0 u1))))))) h

theorem clause3886 (t x04 x05 x45 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ ((t + ((-1) * x05) + x45) ≥ 1) ∨ (¬ (x04 ≥ 0)) ∨ ((t + ((-1) * x05)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th215 t x04 x05 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u1 u3))))) h

theorem clause3887 (t x05 : ℝ) : ((¬ ((t + ((-1) * x05)) ≤ 0)) ∨ (t ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x05)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x05) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th216 t x05
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3889 (t x05 : ℝ) : ((¬ (t ≤ x05)) ∨ (¬ (x05 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x05 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th217 t x05
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3891 (t x05 : ℝ) (h : (x05 < t)) : ((x05 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 < t) := fun hh => hn hh
  exact u0 h

theorem clause3892 (x04 : ℝ) (h : (x04 ≥ 0)) : ((x04 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause3893 (t x45 : ℝ) : ((¬ ((t + ((-1) * x45)) ≤ 0)) ∨ (t ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x45) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th221 t x45
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3895 (t x45 : ℝ) : ((¬ (t ≤ x45)) ∨ (¬ (x45 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x45 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th222 t x45
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause3897 (t x45 : ℝ) (h : (x45 < t)) : ((x45 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 < t) := fun hh => hn hh
  exact u0 h

theorem clause3898 (x68 : ℝ) (h : (x68 ≥ 0)) : ((x68 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause3911 (t x06 x08 x68 : ℝ) : (((x06 + ((-1) * x68)) ≥ 1) ∨ ((x06 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x06 ≤ x08)) ∨ (¬ (x08 ≤ x68)) ∨ (¬ ((x68 - x06) ≥ 1)) ∨ (¬ ((x08 - x06) ≤ (t - 1))) ∨ (¬ ((x68 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th227 t x06 x08 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3936 (t x06 x08 x68 : ℝ) : (((x06 + ((-1) * x68)) ≥ 1) ∨ ((x06 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x68 ≤ x08)) ∨ (¬ (x08 ≤ x06)) ∨ (¬ ((x06 - x68) ≥ 1)) ∨ (¬ ((x06 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th227 t x06 x08 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause3999 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x06 ≤ x08) ∨ (x68 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4000 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x06 ≤ x08) ∨ (x08 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4001 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x06 ≤ x08) ∨ ((x06 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4002 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x06 ≤ x08) ∨ ((x06 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4003 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x06 ≤ x08) ∨ ((x08 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4004 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x08 ≤ x68) ∨ (x68 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4005 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x08 ≤ x68) ∨ (x08 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4006 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x08 ≤ x68) ∨ ((x06 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4007 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x08 ≤ x68) ∨ ((x06 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4008 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : ((x08 ≤ x68) ∨ ((x08 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4009 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x06) ≥ 1) ∨ (x68 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4010 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x06) ≥ 1) ∨ (x08 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4011 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x06) ≥ 1) ∨ ((x06 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4012 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x06) ≥ 1) ∨ ((x06 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4013 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x06) ≥ 1) ∨ ((x08 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4014 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x08 - x06) ≤ (t - 1)) ∨ (x68 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4015 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x08 - x06) ≤ (t - 1)) ∨ (x08 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4016 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x08 - x06) ≤ (t - 1)) ∨ ((x06 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4017 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x08 - x06) ≤ (t - 1)) ∨ ((x06 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4018 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x08 - x06) ≤ (t - 1)) ∨ ((x08 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4019 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x08) ≤ (t - 1)) ∨ (x68 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4020 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x08) ≤ (t - 1)) ∨ (x08 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4021 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x08) ≤ (t - 1)) ∨ ((x06 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4022 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x08) ≤ (t - 1)) ∨ ((x06 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4023 (t x06 x08 x68 : ℝ) (h : (((x06 ≤ x08) ∧ (x08 ≤ x68) ∧ ((x68 - x06) ≥ 1) ∧ ((x08 - x06) ≤ (t - 1)) ∧ ((x68 - x08) ≤ (t - 1))) ∨ ((x68 ≤ x08) ∧ (x08 ≤ x06) ∧ ((x06 - x68) ≥ 1) ∧ ((x06 - x08) ≤ (t - 1)) ∧ ((x08 - x68) ≤ (t - 1))))) : (((x68 - x08) ≤ (t - 1)) ∨ ((x08 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4024 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x56)) ≥ 0) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4026 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x05 + ((-1) * x06)) ≤ 0) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4031 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x06 + ((-1) * x56)) ≤ 0) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4033 (t x05 x06 x56 : ℝ) : (((x06 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x06) + x56) ≥ 1) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4034 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≤ (-1)) ∨ ((x06 + ((-1) * x56)) ≥ 0) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4035 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x06)) ≥ 0) ∨ ((x05 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4036 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x05 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x05 ≤ x06)) ∨ (¬ (x06 ≤ x56)) ∨ (¬ ((x56 - x05) ≥ 1)) ∨ (¬ ((x06 - x05) ≤ (t - 1))) ∨ (¬ ((x56 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4049 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4051 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x05 + ((-1) * x06)) ≤ 0) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th230 t x05 x06 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

#print axioms clause4051
end NineCNFDirectTrial
