import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause6882 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x17 - x13) ≤ (t - 1)) ∨ ((x13 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6883 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x17 - x13) ≤ (t - 1)) ∨ ((x17 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6884 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x17) ≤ (t - 1)) ∨ (x37 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6885 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x17) ≤ (t - 1)) ∨ (x17 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6886 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x17) ≤ (t - 1)) ∨ ((x13 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6887 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x17) ≤ (t - 1)) ∨ ((x13 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6888 (t x13 x17 x37 : ℝ) (h : (((x13 ≤ x17) ∧ (x17 ≤ x37) ∧ ((x37 - x13) ≥ 1) ∧ ((x17 - x13) ≤ (t - 1)) ∧ ((x37 - x17) ≤ (t - 1))) ∨ ((x37 ≤ x17) ∧ (x17 ≤ x13) ∧ ((x13 - x37) ≥ 1) ∧ ((x13 - x17) ≤ (t - 1)) ∧ ((x17 - x37) ≤ (t - 1))))) : (((x37 - x17) ≤ (t - 1)) ∨ ((x17 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6889 (t x14 : ℝ) : ((¬ ((t + ((-1) * x14)) ≤ 0)) ∨ (t ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x14) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th424 t x14
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause6891 (t x14 : ℝ) : ((¬ (t ≤ x14)) ∨ (¬ (x14 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x14 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th425 t x14
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause6893 (t x14 : ℝ) (h : (x14 < t)) : ((x14 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 < t) := fun hh => hn hh
  exact u0 h

theorem clause6894 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x37)) ≥ 0) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6896 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x03 + ((-1) * x07)) ≤ 0) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6900 (t x03 x07 x37 : ℝ) : (((x07 + ((-1) * x37)) ≤ 0) ∨ ((x03 + ((-1) * x07)) ≥ 0) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6901 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x07 + ((-1) * x37)) ≤ 0) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6904 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≤ (-1)) ∨ ((x07 + ((-1) * x37)) ≥ 0) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6906 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x03 + ((-1) * x37)) ≤ (-1)) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6911 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((t + x03 + ((-1) * x07)) ≥ 1) ∨ (¬ (x03 ≤ x07)) ∨ (¬ (x07 ≤ x37)) ∨ (¬ ((x37 - x03) ≥ 1)) ∨ (¬ ((x07 - x03) ≤ (t - 1))) ∨ (¬ ((x37 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6921 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x03 + ((-1) * x07)) ≤ 0) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6926 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x07 + ((-1) * x37)) ≤ 0) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6929 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≤ (-1)) ∨ ((x07 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6930 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≤ (-1)) ∨ ((x03 + ((-1) * x07)) ≥ 0) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6931 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((x03 + ((-1) * x37)) ≤ (-1)) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6936 (t x03 x07 x37 : ℝ) : (((x03 + ((-1) * x37)) ≥ 1) ∨ ((t + x03 + ((-1) * x07)) ≥ 1) ∨ (¬ (x37 ≤ x07)) ∨ (¬ (x07 ≤ x03)) ∨ (¬ ((x03 - x37) ≥ 1)) ∨ (¬ ((x03 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x03 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th428 t x03 x07 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause6994 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x03 ≤ x07) ∨ (x37 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause6995 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x03 ≤ x07) ∨ (x07 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause6996 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x03 ≤ x07) ∨ ((x03 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause6997 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x03 ≤ x07) ∨ ((x03 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause6998 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x03 ≤ x07) ∨ ((x07 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x03 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause6999 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x07 ≤ x37) ∨ (x37 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7000 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x07 ≤ x37) ∨ (x07 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7001 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x07 ≤ x37) ∨ ((x03 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7002 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x07 ≤ x37) ∨ ((x03 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7003 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : ((x07 ≤ x37) ∨ ((x07 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7004 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x03) ≥ 1) ∨ (x37 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7005 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x03) ≥ 1) ∨ (x07 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7006 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x03) ≥ 1) ∨ ((x03 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7007 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x03) ≥ 1) ∨ ((x03 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7008 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x03) ≥ 1) ∨ ((x07 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x03) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7009 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x07 - x03) ≤ (t - 1)) ∨ (x37 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7010 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x07 - x03) ≤ (t - 1)) ∨ (x07 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7011 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x07 - x03) ≤ (t - 1)) ∨ ((x03 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7012 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x07 - x03) ≤ (t - 1)) ∨ ((x03 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7013 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x07 - x03) ≤ (t - 1)) ∨ ((x07 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x03) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7014 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x07) ≤ (t - 1)) ∨ (x37 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7015 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x07) ≤ (t - 1)) ∨ (x07 ≤ x03)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x03) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7016 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x07) ≤ (t - 1)) ∨ ((x03 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7017 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x07) ≤ (t - 1)) ∨ ((x03 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7018 (t x03 x07 x37 : ℝ) (h : (((x03 ≤ x07) ∧ (x07 ≤ x37) ∧ ((x37 - x03) ≥ 1) ∧ ((x07 - x03) ≤ (t - 1)) ∧ ((x37 - x07) ≤ (t - 1))) ∨ ((x37 ≤ x07) ∧ (x07 ≤ x03) ∧ ((x03 - x37) ≥ 1) ∧ ((x03 - x07) ≤ (t - 1)) ∧ ((x07 - x37) ≤ (t - 1))))) : (((x37 - x07) ≤ (t - 1)) ∨ ((x07 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7019 (t x02 x12 x13 x23 x34 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th430 t x02 x12 x13 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u0 (And.intro u1 (And.intro u4 u2))))))) h

theorem clause7020 (t x02 x03 x12 x23 x34 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x03)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th431 t x02 x03 x12 x23 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 u3))))))) h

theorem clause7021 (x35 x45 x57 : ℝ) : ((¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th432 x35 x45 x57
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause7022 (t x03 x12 x23 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x67 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th436 t x03 x12 x23 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u3 (And.intro u5 (And.intro u2 (And.intro u0 u4))))))))) h

theorem clause7023 (t x02 x04 x12 x24 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x56 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x56 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th438 t x02 x04 x12 x24 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u7 (And.intro u5 (And.intro u8 (And.intro u3 (And.intro u6 (And.intro u4 (And.intro u2 u1)))))))))) h

theorem clause7024 (t x56 x57 x67 : ℝ) : ((¬ ((x56 + ((-1) * x67)) ≥ 1)) ∨ ((t + x56 + ((-1) * x57)) ≥ 1) ∨ (¬ (x67 ≥ 0)) ∨ ((t + ((-1) * x57)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x56 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x56 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th439 t x56 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 u0))))) h

theorem clause7025 (t x57 : ℝ) : ((¬ ((t + ((-1) * x57)) ≤ 0)) ∨ (t ≤ x57)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x57)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x57) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th440 t x57
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7027 (t x57 : ℝ) : ((¬ (t ≤ x57)) ∨ (¬ (x57 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x57 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th441 t x57
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7029 (t x57 : ℝ) (h : (x57 < t)) : ((x57 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x57 < t) := fun hh => hn hh
  exact u0 h

theorem clause7030 (t x12 x25 x45 x56 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th443 t x12 x25 x45 x56 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 (And.intro u6 u5)))))))) h

theorem clause7031 (x05 x56 : ℝ) : ((¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th444 x05 x56
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause7032 (x04 x45 x46 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0)) ∨ ((x04 + ((-1) * x46)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th445 x04 x45 x46
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause7033 (x45 x56 : ℝ) : ((¬ ((x45 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th446 x45 x56
  exact (fun hh => (Or.elim hh (fun hh => hh u1) (fun zz => ((fun hh => hh u0) zz)))) h

theorem clause7034 (t x03 x12 x23 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th449 t x03 x12 x23 x34 x45 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 u3)))))))) h

theorem clause7035 (x03 x04 x35 x45 : ℝ) : ((¬ ((x35 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x04)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x04)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th450 x03 x04 x35 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u0 u3))))) h

theorem clause7036 (t x02 x03 x12 x23 x26 x35 x57 x67 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th451 t x02 x03 x12 x23 x26 x35 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u4 (And.intro u3 (And.intro u7 (And.intro u8 (And.intro u5 (And.intro u0 (And.intro u6 u2)))))))))) h

theorem clause7038 (t x04 x12 x24 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1)) ∨ (¬ (x46 ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th453 t x04 x12 x24 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u2 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u6 u3))))))))) h

theorem clause7039 (t x04 x12 x24 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th456 t x04 x12 x24 x46 x56 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u1 (And.intro u4 (And.intro u0 u7)))))))) h

theorem clause7040 (t x02 x12 x24 x26 x34 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th457 t x02 x12 x24 x26 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u7 (And.intro u6 (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u5 u2))))))))) h

theorem clause7041 (x02 x24 x26 : ℝ) : ((¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th458 x02 x24 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause7042 (t x02 x06 x12 x24 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th459 t x02 x06 x12 x24 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u3 (And.intro u4 (And.intro u6 u2)))))))) h

theorem clause7043 (t x24 x34 x35 x45 x57 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0)) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x57)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th462 t x24 x34 x35 x45 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u1))))))) h

theorem clause7044 (x04 x45 x46 : ℝ) : ((¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x46)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x45 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th463 x04 x45 x46
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause7045 (x02 x23 x26 : ℝ) : ((¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th466 x02 x23 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause7046 (t x02 x04 x12 x24 x26 x45 x57 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((t + x57 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x45 + ((-1) * x57)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x57 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x45 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th467 t x02 x04 x12 x24 x26 x45 x57 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u7 (And.intro u0 (And.intro u4 (And.intro u8 (And.intro u5 (And.intro u3 (And.intro u1 u2)))))))))) h

theorem clause7047 (x01 x02 x15 x25 : ℝ) : ((¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x15 + ((-1) * x25)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x15)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x15)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th468 x01 x02 x15 x25
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u2 (And.intro u1 u0)))) h

theorem clause7048 (x02 x12 x23 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x12)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x12)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th469 x02 x12 x23
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause7049 (x12 x25 : ℝ) : ((¬ ((x12 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th470 x12 x25
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause7050 (x05 x06 x15 x56 : ℝ) : ((¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th471 x05 x06 x15 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u3 (And.intro u2 u1))))) h

theorem clause7051 (x03 x13 x23 : ℝ) : ((¬ ((x03 + ((-1) * x13)) ≥ 0)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ ((x03 + ((-1) * x23)) ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x13)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((x03 + ((-1) * x23)) ≥ 0) := fun hh => hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th474 x03 x13 x23
  exact (fun hh => u2 (hh (And.intro u0 u1))) h

theorem clause7052 (t x01 x13 x34 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th478 t x01 x13 x34 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u3 (And.intro u6 u0)))))))) h

theorem clause7053 (x01 : ℝ) (h : (x01 ≥ 0)) : ((x01 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause7054 (t x67 : ℝ) : ((¬ ((t + ((-1) * x67)) ≤ 0)) ∨ (t ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x67)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x67) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th480 t x67
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7056 (t x67 : ℝ) : ((¬ (t ≤ x67)) ∨ (¬ (x67 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x67 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th481 t x67
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7058 (t x67 : ℝ) (h : (x67 < t)) : ((x67 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 < t) := fun hh => hn hh
  exact u0 h

theorem clause7059 (t x13 x15 x34 x35 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x15)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x15)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th484 t x13 x15 x34 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u1 (And.intro u4 (And.intro u2 u0))))))) h

theorem clause7060 (t x01 x13 x35 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x35 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th485 t x01 x13 x35 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u0 (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u6 u1)))))))) h

theorem clause7061 (t x02 x12 x13 x23 x25 x26 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))))
  have u9 : ((x13 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))
  have h := NineTheoryTrial.th486 t x02 x12 x13 x23 x25 x26 x36 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u9 (And.intro u4 (And.intro u3 (And.intro u8 (And.intro u5 (And.intro u6 u7))))))))))) h

theorem clause7062 (t x02 x05 x12 x25 x26 x36 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((t + ((-1) * x36) + x56) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x36) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th488 t x02 x05 x12 x25 x26 x36 x56 x67
  exact (fun hh => (fun hh => hh u6) (hh (And.intro u2 (And.intro u4 (And.intro u7 (And.intro u3 (And.intro u0 (And.intro u1 (And.intro u5 u8))))))))) h

theorem clause7065 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x13 + ((-1) * x16)) ≤ 0) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7066 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x16)) ≤ 0) ∨ ((t + ((-1) * x13) + x16) ≥ 1) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7069 (t x13 x16 x36 : ℝ) : (((x16 + ((-1) * x36)) ≤ 0) ∨ ((x13 + ((-1) * x16)) ≥ 0) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7070 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x16 + ((-1) * x36)) ≤ 0) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7073 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((x16 + ((-1) * x36)) ≥ 0) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7074 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((x13 + ((-1) * x16)) ≥ 0) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7075 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x13 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7077 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x36) ≥ 1) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7080 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((t + x13 + ((-1) * x16)) ≥ 1) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7085 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((t + x16 + ((-1) * x36)) ≥ 1) ∨ (¬ (x13 ≤ x16)) ∨ (¬ (x16 ≤ x36)) ∨ (¬ ((x36 - x13) ≥ 1)) ∨ (¬ ((x16 - x13) ≤ (t - 1))) ∨ (¬ ((x36 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x16 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7090 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x13 + ((-1) * x16)) ≤ 0) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7091 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x16)) ≤ 0) ∨ ((t + ((-1) * x13) + x16) ≥ 1) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x16) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7094 (t x13 x16 x36 : ℝ) : (((x16 + ((-1) * x36)) ≤ 0) ∨ ((x13 + ((-1) * x16)) ≥ 0) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7095 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x16 + ((-1) * x36)) ≤ 0) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7098 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((x16 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7099 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((x13 + ((-1) * x16)) ≥ 0) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7100 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((x13 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7102 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x36) ≥ 1) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7105 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((t + x13 + ((-1) * x16)) ≥ 1) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x13 + ((-1) * x16)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7110 (t x13 x16 x36 : ℝ) : (((x13 + ((-1) * x36)) ≥ 1) ∨ ((t + x16 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x16)) ∨ (¬ (x16 ≤ x13)) ∨ (¬ ((x13 - x36) ≥ 1)) ∨ (¬ ((x13 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x16 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th490 t x13 x16 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7163 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x13 ≤ x16) ∨ (x36 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7164 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x13 ≤ x16) ∨ (x16 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7165 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x13 ≤ x16) ∨ ((x13 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7166 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x13 ≤ x16) ∨ ((x13 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7167 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x13 ≤ x16) ∨ ((x16 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7168 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x16 ≤ x36) ∨ (x36 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7169 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x16 ≤ x36) ∨ (x16 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7170 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x16 ≤ x36) ∨ ((x13 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7171 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x16 ≤ x36) ∨ ((x13 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7172 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : ((x16 ≤ x36) ∨ ((x16 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7173 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x13) ≥ 1) ∨ (x36 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7174 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x13) ≥ 1) ∨ (x16 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7175 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x13) ≥ 1) ∨ ((x13 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7176 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x13) ≥ 1) ∨ ((x13 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7177 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x13) ≥ 1) ∨ ((x16 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7178 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x16 - x13) ≤ (t - 1)) ∨ (x36 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7179 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x16 - x13) ≤ (t - 1)) ∨ (x16 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7180 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x16 - x13) ≤ (t - 1)) ∨ ((x13 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7181 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x16 - x13) ≤ (t - 1)) ∨ ((x13 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7182 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x16 - x13) ≤ (t - 1)) ∨ ((x16 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7183 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x16) ≤ (t - 1)) ∨ (x36 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7184 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x16) ≤ (t - 1)) ∨ (x16 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7185 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x16) ≤ (t - 1)) ∨ ((x13 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7186 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x16) ≤ (t - 1)) ∨ ((x13 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7187 (t x13 x16 x36 : ℝ) (h : (((x13 ≤ x16) ∧ (x16 ≤ x36) ∧ ((x36 - x13) ≥ 1) ∧ ((x16 - x13) ≤ (t - 1)) ∧ ((x36 - x16) ≤ (t - 1))) ∨ ((x36 ≤ x16) ∧ (x16 ≤ x13) ∧ ((x13 - x36) ≥ 1) ∧ ((x13 - x16) ≤ (t - 1)) ∧ ((x16 - x36) ≤ (t - 1))))) : (((x36 - x16) ≤ (t - 1)) ∨ ((x16 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7188 (t x02 x12 x23 x26 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ ((t + ((-1) * x12)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x56)) ≥ 0)) ∨ (¬ (x45 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x12)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : (x45 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th493 t x02 x12 x23 x26 x45 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u2 (And.intro u3 (And.intro u5 (And.intro u7 (And.intro u4 u6))))))))) h

theorem clause7190 (t x12 x14 x23 x24 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x23 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x14)) ≤ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x23 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x14)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th498 t x12 x14 x23 x24 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u4 (And.intro u1 (And.intro u2 (And.intro u5 u0))))))) h

theorem clause7191 (t x23 x24 x34 : ℝ) : (((t + ((-1) * x24)) ≤ 0) ∨ ((t + x23 + ((-1) * x24)) ≥ 1) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1)) ∨ (¬ (x34 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th499 t x23 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u3 u2))))) h

theorem clause7192 (x14 x24 x45 : ℝ) : ((¬ ((x24 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th500 x14 x24 x45
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause7193 (t x04 x05 x24 x34 x45 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x24) + x34) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x24) + x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th501 t x04 x05 x24 x34 x45 x56
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u4 (And.intro u0 (And.intro u5 (And.intro u1 (And.intro u6 u3))))))) h

theorem clause7194 (t x05 x15 x34 x45 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≤ 0)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + ((-1) * x15) + x45) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x15)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x15) + x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th502 t x05 x15 x34 x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u6 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u3 u2)))))))) h

theorem clause7195 (t x04 x05 x45 x47 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x05)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≤ (-1))) ∨ (¬ ((t + x45 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x05)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x47)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x45 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th503 t x04 x05 x45 x47 x56
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u1 (And.intro u3 (And.intro u2 (And.intro u0 u5)))))) h

theorem clause7197 (t x02 x03 x12 x23 x26 x34 x47 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + x02 + ((-1) * x12)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x23)) ≤ 0)) ∨ (¬ ((t + x47 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x02 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x23)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x47 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th507 t x02 x03 x12 x23 x26 x34 x47 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u1 (And.intro u4 (And.intro u0 (And.intro u8 (And.intro u7 (And.intro u2 (And.intro u5 u6))))))))) h

theorem clause7200 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x34 + ((-1) * x37)) ≤ 0) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7204 (t x34 x37 x47 : ℝ) : (((x37 + ((-1) * x47)) ≤ 0) ∨ ((x34 + ((-1) * x37)) ≥ 0) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7205 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x37 + ((-1) * x47)) ≤ 0) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7208 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((x37 + ((-1) * x47)) ≥ 0) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7209 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((x34 + ((-1) * x37)) ≥ 0) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7210 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x34 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7211 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x34) + x37) ≥ 1) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7212 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x47) ≥ 1) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7215 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((t + x34 + ((-1) * x37)) ≥ 1) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7220 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((t + x37 + ((-1) * x47)) ≥ 1) ∨ (¬ (x34 ≤ x37)) ∨ (¬ (x37 ≤ x47)) ∨ (¬ ((x47 - x34) ≥ 1)) ∨ (¬ ((x37 - x34) ≤ (t - 1))) ∨ (¬ ((x47 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x37 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7223 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x37)) ≤ 0) ∨ ((x37 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7225 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x34 + ((-1) * x37)) ≤ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7229 (t x34 x37 x47 : ℝ) : (((x37 + ((-1) * x47)) ≤ 0) ∨ ((x34 + ((-1) * x37)) ≥ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7230 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x37 + ((-1) * x47)) ≤ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7233 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((x37 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7234 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((x34 + ((-1) * x37)) ≥ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7235 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((x34 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7236 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x34) + x37) ≥ 1) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7237 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x37) + x47) ≥ 1) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x37) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7239 (t x34 x37 x47 : ℝ) : (((t + x34 + ((-1) * x37)) ≥ 1) ∨ ((x34 + ((-1) * x37)) ≥ 0) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x34 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7240 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((t + x34 + ((-1) * x37)) ≥ 1) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7245 (t x34 x37 x47 : ℝ) : (((x34 + ((-1) * x47)) ≥ 1) ∨ ((t + x37 + ((-1) * x47)) ≥ 1) ∨ (¬ (x47 ≤ x37)) ∨ (¬ (x37 ≤ x34)) ∨ (¬ ((x34 - x47) ≥ 1)) ∨ (¬ ((x34 - x37) ≤ (t - 1))) ∨ (¬ ((x37 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x37 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x37 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th509 t x34 x37 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7298 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x34 ≤ x37) ∨ (x47 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7299 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x34 ≤ x37) ∨ (x37 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7300 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x34 ≤ x37) ∨ ((x34 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7301 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x34 ≤ x37) ∨ ((x34 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7302 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x34 ≤ x37) ∨ ((x37 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7303 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x37 ≤ x47) ∨ (x47 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7304 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x37 ≤ x47) ∨ (x37 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7305 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x37 ≤ x47) ∨ ((x34 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7306 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x37 ≤ x47) ∨ ((x34 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7307 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : ((x37 ≤ x47) ∨ ((x37 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x37 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7308 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x34) ≥ 1) ∨ (x47 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7309 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x34) ≥ 1) ∨ (x37 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7310 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x34) ≥ 1) ∨ ((x34 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7311 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x34) ≥ 1) ∨ ((x34 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7312 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x34) ≥ 1) ∨ ((x37 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7313 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x37 - x34) ≤ (t - 1)) ∨ (x47 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7314 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x37 - x34) ≤ (t - 1)) ∨ (x37 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7315 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x37 - x34) ≤ (t - 1)) ∨ ((x34 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7316 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x37 - x34) ≤ (t - 1)) ∨ ((x34 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7317 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x37 - x34) ≤ (t - 1)) ∨ ((x37 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7318 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x37) ≤ (t - 1)) ∨ (x47 ≤ x37)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x37) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7319 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x37) ≤ (t - 1)) ∨ (x37 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7320 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x37) ≤ (t - 1)) ∨ ((x34 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7321 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x37) ≤ (t - 1)) ∨ ((x34 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7322 (t x34 x37 x47 : ℝ) (h : (((x34 ≤ x37) ∧ (x37 ≤ x47) ∧ ((x47 - x34) ≥ 1) ∧ ((x37 - x34) ≤ (t - 1)) ∧ ((x47 - x37) ≤ (t - 1))) ∨ ((x47 ≤ x37) ∧ (x37 ≤ x34) ∧ ((x34 - x47) ≥ 1) ∧ ((x34 - x37) ≤ (t - 1)) ∧ ((x37 - x47) ≤ (t - 1))))) : (((x47 - x37) ≤ (t - 1)) ∨ ((x37 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x37) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x37 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7323 (x12 x23 x24 : ℝ) : ((¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≥ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x24)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th512 x12 x23 x24
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause7324 (x06 x46 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ (¬ ((x06 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th514 x06 x46 x67
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause7327 (x17 : ℝ) (h : (x17 ≥ 0)) : ((x17 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause7328 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x17)) ≥ 0) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7330 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x01 + ((-1) * x07)) ≤ 0) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7334 (t x01 x07 x17 : ℝ) : (((x07 + ((-1) * x17)) ≤ 0) ∨ ((x01 + ((-1) * x07)) ≥ 0) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7335 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x07 + ((-1) * x17)) ≤ 0) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7338 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≤ (-1)) ∨ ((x07 + ((-1) * x17)) ≥ 0) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7340 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x01 + ((-1) * x17)) ≤ (-1)) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7341 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x07) ≥ 1) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x07) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7345 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((t + x01 + ((-1) * x07)) ≥ 1) ∨ (¬ (x01 ≤ x07)) ∨ (¬ (x07 ≤ x17)) ∨ (¬ ((x17 - x01) ≥ 1)) ∨ (¬ ((x07 - x01) ≤ (t - 1))) ∨ (¬ ((x17 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x01 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x17 - x01) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x01) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7355 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x01 + ((-1) * x07)) ≤ 0) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7359 (t x01 x07 x17 : ℝ) : (((x07 + ((-1) * x17)) ≤ 0) ∨ ((x01 + ((-1) * x07)) ≥ 0) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7360 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x07 + ((-1) * x17)) ≤ 0) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7363 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≤ (-1)) ∨ ((x07 + ((-1) * x17)) ≥ 0) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7365 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((x01 + ((-1) * x17)) ≤ (-1)) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7366 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≤ (-1)) ∨ ((t + ((-1) * x01) + x07) ≥ 1) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x01) + x07) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7370 (t x01 x07 x17 : ℝ) : (((x01 + ((-1) * x17)) ≥ 1) ∨ ((t + x01 + ((-1) * x07)) ≥ 1) ∨ (¬ (x17 ≤ x07)) ∨ (¬ (x07 ≤ x01)) ∨ (¬ ((x01 - x17) ≥ 1)) ∨ (¬ ((x01 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x01 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x17 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x01) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x01 - x17) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th520 t x01 x07 x17
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7428 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x01 ≤ x07) ∨ (x17 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7429 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x01 ≤ x07) ∨ (x07 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7430 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x01 ≤ x07) ∨ ((x01 - x17) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x17) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7431 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x01 ≤ x07) ∨ ((x01 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7432 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x01 ≤ x07) ∨ ((x07 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x01 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7433 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x07 ≤ x17) ∨ (x17 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7434 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x07 ≤ x17) ∨ (x07 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7435 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x07 ≤ x17) ∨ ((x01 - x17) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x17) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7436 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x07 ≤ x17) ∨ ((x01 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7437 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : ((x07 ≤ x17) ∨ ((x07 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7438 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x01) ≥ 1) ∨ (x17 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7439 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x01) ≥ 1) ∨ (x07 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7440 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x01) ≥ 1) ∨ ((x01 - x17) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x17) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7441 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x01) ≥ 1) ∨ ((x01 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7442 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x01) ≥ 1) ∨ ((x07 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x01) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7443 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x07 - x01) ≤ (t - 1)) ∨ (x17 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7444 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x07 - x01) ≤ (t - 1)) ∨ (x07 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7445 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x07 - x01) ≤ (t - 1)) ∨ ((x01 - x17) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x17) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7446 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x07 - x01) ≤ (t - 1)) ∨ ((x01 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7447 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x07 - x01) ≤ (t - 1)) ∨ ((x07 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x01) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7448 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x07) ≤ (t - 1)) ∨ (x17 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7449 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x07) ≤ (t - 1)) ∨ (x07 ≤ x01)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x01) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7450 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x07) ≤ (t - 1)) ∨ ((x01 - x17) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x17) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7451 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x07) ≤ (t - 1)) ∨ ((x01 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x01 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7452 (t x01 x07 x17 : ℝ) (h : (((x01 ≤ x07) ∧ (x07 ≤ x17) ∧ ((x17 - x01) ≥ 1) ∧ ((x07 - x01) ≤ (t - 1)) ∧ ((x17 - x07) ≤ (t - 1))) ∨ ((x17 ≤ x07) ∧ (x07 ≤ x01) ∧ ((x01 - x17) ≥ 1) ∧ ((x01 - x07) ≤ (t - 1)) ∧ ((x07 - x17) ≤ (t - 1))))) : (((x17 - x07) ≤ (t - 1)) ∨ ((x07 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7453 (x01 x12 x13 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th522 x01 x12 x13
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u2 u0))) h

theorem clause7454 (x01 x02 x13 x23 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x02)) ≤ 0)) ∨ ((x02 + ((-1) * x23)) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((x02 + ((-1) * x23)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th523 x01 x02 x13 x23
  exact (fun hh => u3 (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause7456 (t x01 x12 x13 x23 x27 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x23)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x12)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x27)) ≤ (-1))) ∨ (¬ ((t + x23 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x23)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x12)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 + ((-1) * x27)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + x23 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th525 t x01 x12 x13 x23 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u3 (And.intro u5 u4))))))) h

theorem clause7458 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≥ 0) ∨ ((x23 + ((-1) * x27)) ≤ 0) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7459 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≤ 0) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7460 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≤ 0) ∨ ((t + ((-1) * x23) + x27) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7464 (t x23 x27 x37 : ℝ) : (((x27 + ((-1) * x37)) ≤ 0) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7466 (t x23 x27 x37 : ℝ) : (((x27 + ((-1) * x37)) ≤ 0) ∨ ((t + ((-1) * x27) + x37) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7467 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x27 + ((-1) * x37)) ≥ 0) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7468 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x23 + ((-1) * x27)) ≥ 0) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7469 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7470 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x23) + x27) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7471 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x37) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7473 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≥ 0) ∨ ((t + x23 + ((-1) * x27)) ≥ 1) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7477 (t x23 x27 x37 : ℝ) : (((t + x27 + ((-1) * x37)) ≥ 1) ∨ ((x27 + ((-1) * x37)) ≥ 0) ∨ (¬ (x23 ≤ x27)) ∨ (¬ (x27 ≤ x37)) ∨ (¬ ((x37 - x23) ≥ 1)) ∨ (¬ ((x27 - x23) ≤ (t - 1))) ∨ (¬ ((x37 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x27 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x37) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x37 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x37 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7482 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7483 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≥ 0) ∨ ((x23 + ((-1) * x27)) ≤ 0) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7484 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≤ 0) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7485 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≤ 0) ∨ ((t + ((-1) * x23) + x27) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x27) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7489 (t x23 x27 x37 : ℝ) : (((x27 + ((-1) * x37)) ≤ 0) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x37)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7492 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x27 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7493 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x23 + ((-1) * x27)) ≥ 0) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7494 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((x23 + ((-1) * x37)) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7496 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x37)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x37) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x37)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x37) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7498 (t x23 x27 x37 : ℝ) : (((x23 + ((-1) * x27)) ≥ 0) ∨ ((t + x23 + ((-1) * x27)) ≥ 1) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7502 (t x23 x27 x37 : ℝ) : (((t + x27 + ((-1) * x37)) ≥ 1) ∨ ((x27 + ((-1) * x37)) ≥ 0) ∨ (¬ (x37 ≤ x27)) ∨ (¬ (x27 ≤ x23)) ∨ (¬ ((x23 - x37) ≥ 1)) ∨ (¬ ((x23 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x37) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x27 + ((-1) * x37)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x37)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x37 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x37) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x37) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th527 t x23 x27 x37
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7557 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x23 ≤ x27) ∨ (x37 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7558 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x23 ≤ x27) ∨ (x27 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7559 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x23 ≤ x27) ∨ ((x23 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7560 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x23 ≤ x27) ∨ ((x23 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7561 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x23 ≤ x27) ∨ ((x27 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7562 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x27 ≤ x37) ∨ (x37 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7563 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x27 ≤ x37) ∨ (x27 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7564 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x27 ≤ x37) ∨ ((x23 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7565 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x27 ≤ x37) ∨ ((x23 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7566 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : ((x27 ≤ x37) ∨ ((x27 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x37) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7567 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x23) ≥ 1) ∨ (x37 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7568 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x23) ≥ 1) ∨ (x27 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7569 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x23) ≥ 1) ∨ ((x23 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7570 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x23) ≥ 1) ∨ ((x23 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7571 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x23) ≥ 1) ∨ ((x27 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7572 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x27 - x23) ≤ (t - 1)) ∨ (x37 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7573 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x27 - x23) ≤ (t - 1)) ∨ (x27 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7574 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x27 - x23) ≤ (t - 1)) ∨ ((x23 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7575 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x27 - x23) ≤ (t - 1)) ∨ ((x23 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7576 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x27 - x23) ≤ (t - 1)) ∨ ((x27 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7577 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x27) ≤ (t - 1)) ∨ (x37 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x37 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7578 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x27) ≤ (t - 1)) ∨ (x27 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7579 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x27) ≤ (t - 1)) ∨ ((x23 - x37) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x37) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7580 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x27) ≤ (t - 1)) ∨ ((x23 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7581 (t x23 x27 x37 : ℝ) (h : (((x23 ≤ x27) ∧ (x27 ≤ x37) ∧ ((x37 - x23) ≥ 1) ∧ ((x27 - x23) ≤ (t - 1)) ∧ ((x37 - x27) ≤ (t - 1))) ∨ ((x37 ≤ x27) ∧ (x27 ≤ x23) ∧ ((x23 - x37) ≥ 1) ∧ ((x23 - x27) ≤ (t - 1)) ∧ ((x27 - x37) ≤ (t - 1))))) : (((x37 - x27) ≤ (t - 1)) ∨ ((x27 - x37) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x37 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x37) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7584 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≤ 0) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7588 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((x17 + ((-1) * x27)) ≤ 0) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7589 (t x12 x17 x27 : ℝ) : (((x17 + ((-1) * x27)) ≤ 0) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7592 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((x17 + ((-1) * x27)) ≥ 0) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7593 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((x12 + ((-1) * x27)) ≤ (-1)) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7594 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7595 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x17) ≥ 1) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x17) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7598 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((t + x12 + ((-1) * x17)) ≥ 1) ∨ (¬ (x12 ≤ x17)) ∨ (¬ (x17 ≤ x27)) ∨ (¬ ((x27 - x12) ≥ 1)) ∨ (¬ ((x17 - x12) ≤ (t - 1))) ∨ (¬ ((x27 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x12 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7609 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≤ 0) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7613 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((x17 + ((-1) * x27)) ≤ 0) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7614 (t x12 x17 x27 : ℝ) : (((x17 + ((-1) * x27)) ≤ 0) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7617 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((x17 + ((-1) * x27)) ≥ 0) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7618 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((x12 + ((-1) * x27)) ≤ (-1)) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7619 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((x12 + ((-1) * x27)) ≥ 1) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7620 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x27)) ≤ (-1)) ∨ ((t + ((-1) * x12) + x17) ≥ 1) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x17) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7623 (t x12 x17 x27 : ℝ) : (((x12 + ((-1) * x17)) ≥ 0) ∨ ((t + x12 + ((-1) * x17)) ≥ 1) ∨ (¬ (x27 ≤ x17)) ∨ (¬ (x17 ≤ x12)) ∨ (¬ ((x12 - x27) ≥ 1)) ∨ (¬ ((x12 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x12 + ((-1) * x17)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th530 t x12 x17 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7682 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x12 ≤ x17) ∨ (x27 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7683 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x12 ≤ x17) ∨ (x17 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7684 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x12 ≤ x17) ∨ ((x12 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7685 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x12 ≤ x17) ∨ ((x12 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7686 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x12 ≤ x17) ∨ ((x17 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7687 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x17 ≤ x27) ∨ (x27 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7688 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x17 ≤ x27) ∨ (x17 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7689 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x17 ≤ x27) ∨ ((x12 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7690 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x17 ≤ x27) ∨ ((x12 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7691 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : ((x17 ≤ x27) ∨ ((x17 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7692 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x12) ≥ 1) ∨ (x27 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7693 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x12) ≥ 1) ∨ (x17 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7694 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x12) ≥ 1) ∨ ((x12 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7695 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x12) ≥ 1) ∨ ((x12 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7696 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x12) ≥ 1) ∨ ((x17 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7697 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x17 - x12) ≤ (t - 1)) ∨ (x27 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7698 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x17 - x12) ≤ (t - 1)) ∨ (x17 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7699 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x17 - x12) ≤ (t - 1)) ∨ ((x12 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7700 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x17 - x12) ≤ (t - 1)) ∨ ((x12 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7701 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x17 - x12) ≤ (t - 1)) ∨ ((x17 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x12) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7702 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x17) ≤ (t - 1)) ∨ (x27 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7703 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x17) ≤ (t - 1)) ∨ (x17 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7704 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x17) ≤ (t - 1)) ∨ ((x12 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7705 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x17) ≤ (t - 1)) ∨ ((x12 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7706 (t x12 x17 x27 : ℝ) (h : (((x12 ≤ x17) ∧ (x17 ≤ x27) ∧ ((x27 - x12) ≥ 1) ∧ ((x17 - x12) ≤ (t - 1)) ∧ ((x27 - x17) ≤ (t - 1))) ∨ ((x27 ≤ x17) ∧ (x17 ≤ x12) ∧ ((x12 - x27) ≥ 1) ∧ ((x12 - x17) ≤ (t - 1)) ∧ ((x17 - x27) ≤ (t - 1))))) : (((x27 - x17) ≤ (t - 1)) ∨ ((x17 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7707 (t x12 x23 x24 x34 x36 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th536 t x12 x23 x24 x34 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 (And.intro u5 u4))))))) h

theorem clause7708 (t x12 x23 x24 x34 x35 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x12 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x34) + x35) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x24 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th537 t x12 x23 x24 x34 x35
  exact (fun hh => (fun hh => hh u4) (hh (And.intro u3 (And.intro u1 (And.intro u0 (And.intro u2 u5)))))) h

theorem clause7709 (t x01 x14 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ ((x36 + ((-1) * x67)) ≥ 1)) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th542 t x01 x14 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u3 u2)))))))) h

theorem clause7710 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7712 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x16 + ((-1) * x17)) ≤ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7716 (t x16 x17 x67 : ℝ) : (((x17 + ((-1) * x67)) ≤ 0) ∨ ((x16 + ((-1) * x17)) ≥ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7717 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x17 + ((-1) * x67)) ≤ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7719 (t x16 x17 x67 : ℝ) : (((x17 + ((-1) * x67)) ≤ 0) ∨ ((t + ((-1) * x17) + x67) ≥ 1) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7720 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≤ (-1)) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7722 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x16 + ((-1) * x67)) ≤ (-1)) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7724 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x67) ≥ 1) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7730 (t x16 x17 x67 : ℝ) : (((t + x17 + ((-1) * x67)) ≥ 1) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x16 ≤ x17)) ∨ (¬ (x17 ≤ x67)) ∨ (¬ ((x67 - x16) ≥ 1)) ∨ (¬ ((x17 - x16) ≤ (t - 1))) ∨ (¬ ((x67 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x17 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x16 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x16) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7735 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7737 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x16 + ((-1) * x17)) ≤ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7741 (t x16 x17 x67 : ℝ) : (((x17 + ((-1) * x67)) ≤ 0) ∨ ((x16 + ((-1) * x17)) ≥ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7742 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x17 + ((-1) * x67)) ≤ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7744 (t x16 x17 x67 : ℝ) : (((x17 + ((-1) * x67)) ≤ 0) ∨ ((t + ((-1) * x17) + x67) ≥ 1) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7745 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≤ (-1)) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7747 (t x16 x17 x67 : ℝ) : (((x16 + ((-1) * x67)) ≥ 1) ∨ ((x16 + ((-1) * x67)) ≤ (-1)) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7755 (t x16 x17 x67 : ℝ) : (((t + x17 + ((-1) * x67)) ≥ 1) ∨ ((x17 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x17)) ∨ (¬ (x17 ≤ x16)) ∨ (¬ ((x16 - x67) ≥ 1)) ∨ (¬ ((x16 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x17 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x16 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th544 t x16 x17 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7810 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x16 ≤ x17) ∨ (x67 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7811 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x16 ≤ x17) ∨ (x17 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7812 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x16 ≤ x17) ∨ ((x16 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7813 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x16 ≤ x17) ∨ ((x16 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7814 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x16 ≤ x17) ∨ ((x17 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7815 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x17 ≤ x67) ∨ (x67 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7816 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x17 ≤ x67) ∨ (x17 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7817 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x17 ≤ x67) ∨ ((x16 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7818 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x17 ≤ x67) ∨ ((x16 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7819 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : ((x17 ≤ x67) ∨ ((x17 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7820 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x16) ≥ 1) ∨ (x67 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7821 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x16) ≥ 1) ∨ (x17 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7822 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x16) ≥ 1) ∨ ((x16 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7823 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x16) ≥ 1) ∨ ((x16 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7824 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x16) ≥ 1) ∨ ((x17 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x16) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7825 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x17 - x16) ≤ (t - 1)) ∨ (x67 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7826 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x17 - x16) ≤ (t - 1)) ∨ (x17 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7827 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x17 - x16) ≤ (t - 1)) ∨ ((x16 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7828 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x17 - x16) ≤ (t - 1)) ∨ ((x16 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7829 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x17 - x16) ≤ (t - 1)) ∨ ((x17 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7830 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x17) ≤ (t - 1)) ∨ (x67 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7831 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x17) ≤ (t - 1)) ∨ (x17 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7832 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x17) ≤ (t - 1)) ∨ ((x16 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7833 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x17) ≤ (t - 1)) ∨ ((x16 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7834 (t x16 x17 x67 : ℝ) (h : (((x16 ≤ x17) ∧ (x17 ≤ x67) ∧ ((x67 - x16) ≥ 1) ∧ ((x17 - x16) ≤ (t - 1)) ∧ ((x67 - x17) ≤ (t - 1))) ∨ ((x67 ≤ x17) ∧ (x17 ≤ x16) ∧ ((x16 - x67) ≥ 1) ∧ ((x16 - x17) ≤ (t - 1)) ∧ ((x17 - x67) ≤ (t - 1))))) : (((x67 - x17) ≤ (t - 1)) ∨ ((x17 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7836 (x26 x46 x56 : ℝ) : ((¬ ((x46 + ((-1) * x56)) ≥ 0)) ∨ ((x26 + ((-1) * x46)) ≤ 0) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th548 x26 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause7837 (x12 x24 x25 : ℝ) : ((¬ ((x24 + ((-1) * x25)) ≤ 0)) ∨ (¬ ((x12 + ((-1) * x24)) ≤ (-1))) ∨ (¬ ((x12 + ((-1) * x25)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x24 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x12 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x12 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th552 x12 x24 x25
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 u1))) h

theorem clause7839 (x05 x25 x57 : ℝ) : ((¬ ((x05 + ((-1) * x25)) ≤ 0)) ∨ ((x05 + ((-1) * x57)) ≤ (-1)) ∨ (¬ ((x25 + ((-1) * x57)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x05 + ((-1) * x25)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th556 x05 x25 x57
  exact (fun hh => u1 (hh (And.intro u2 u0))) h

theorem clause7840 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x57)) ≥ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7842 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((x15 + ((-1) * x17)) ≤ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7847 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((x17 + ((-1) * x57)) ≤ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7849 (t x15 x17 x57 : ℝ) : (((x17 + ((-1) * x57)) ≤ 0) ∨ ((t + ((-1) * x17) + x57) ≥ 1) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7850 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x17 + ((-1) * x57)) ≥ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7851 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x15 + ((-1) * x17)) ≥ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7852 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x15 + ((-1) * x57)) ≥ 1) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7854 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x57) ≥ 1) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7860 (t x15 x17 x57 : ℝ) : (((t + x17 + ((-1) * x57)) ≥ 1) ∨ ((x17 + ((-1) * x57)) ≥ 0) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x17 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7862 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((t + x17 + ((-1) * x57)) ≥ 1) ∨ (¬ (x15 ≤ x17)) ∨ (¬ (x17 ≤ x57)) ∨ (¬ ((x57 - x15) ≥ 1)) ∨ (¬ ((x17 - x15) ≤ (t - 1))) ∨ (¬ ((x57 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x17 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x57) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x57 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x57 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7865 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7867 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((x15 + ((-1) * x17)) ≤ 0) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7872 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((x17 + ((-1) * x57)) ≤ 0) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7874 (t x15 x17 x57 : ℝ) : (((x17 + ((-1) * x57)) ≤ 0) ∨ ((t + ((-1) * x17) + x57) ≥ 1) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x57)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7875 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x17 + ((-1) * x57)) ≥ 0) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x57)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7876 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x15 + ((-1) * x17)) ≥ 0) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7877 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((x15 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7879 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x57) ≥ 1) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x57) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7887 (t x15 x17 x57 : ℝ) : (((x15 + ((-1) * x57)) ≥ 1) ∨ ((t + x17 + ((-1) * x57)) ≥ 1) ∨ (¬ (x57 ≤ x17)) ∨ (¬ (x17 ≤ x15)) ∨ (¬ ((x15 - x57) ≥ 1)) ∨ (¬ ((x15 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x57) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x17 + ((-1) * x57)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x57 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x57) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x57) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th559 t x15 x17 x57
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7940 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x15 ≤ x17) ∨ (x57 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7941 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x15 ≤ x17) ∨ (x17 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7942 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x15 ≤ x17) ∨ ((x15 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7943 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x15 ≤ x17) ∨ ((x15 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7944 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x15 ≤ x17) ∨ ((x17 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7945 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x17 ≤ x57) ∨ (x57 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7946 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x17 ≤ x57) ∨ (x17 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7947 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x17 ≤ x57) ∨ ((x15 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7948 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x17 ≤ x57) ∨ ((x15 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7949 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : ((x17 ≤ x57) ∨ ((x17 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x57) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7950 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x15) ≥ 1) ∨ (x57 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7951 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x15) ≥ 1) ∨ (x17 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7952 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x15) ≥ 1) ∨ ((x15 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7953 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x15) ≥ 1) ∨ ((x15 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7954 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x15) ≥ 1) ∨ ((x17 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7955 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x17 - x15) ≤ (t - 1)) ∨ (x57 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7956 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x17 - x15) ≤ (t - 1)) ∨ (x17 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7957 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x17 - x15) ≤ (t - 1)) ∨ ((x15 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7958 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x17 - x15) ≤ (t - 1)) ∨ ((x15 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7959 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x17 - x15) ≤ (t - 1)) ∨ ((x17 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7960 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x17) ≤ (t - 1)) ∨ (x57 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x57 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause7961 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x17) ≤ (t - 1)) ∨ (x17 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause7962 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x17) ≤ (t - 1)) ∨ ((x15 - x57) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x57) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause7963 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x17) ≤ (t - 1)) ∨ ((x15 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause7964 (t x15 x17 x57 : ℝ) (h : (((x15 ≤ x17) ∧ (x17 ≤ x57) ∧ ((x57 - x15) ≥ 1) ∧ ((x17 - x15) ≤ (t - 1)) ∧ ((x57 - x17) ≤ (t - 1))) ∨ ((x57 ≤ x17) ∧ (x17 ≤ x15) ∧ ((x15 - x57) ≥ 1) ∧ ((x15 - x17) ≤ (t - 1)) ∧ ((x17 - x57) ≤ (t - 1))))) : (((x57 - x17) ≤ (t - 1)) ∨ ((x17 - x57) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x57 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x57) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause7965 (t x01 x03 x13 x15 x35 x36 x57 : ℝ) : ((¬ ((x03 + ((-1) * x36)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((x35 + ((-1) * x57)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x03)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x36)) ≥ 1)) ∨ ((t + ((-1) * x35)) ≤ 0) ∨ (¬ ((x13 + ((-1) * x15)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x57)) ≤ (-1))) ∨ (¬ (x01 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x35 + ((-1) * x57)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x03)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x13 + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x15 + ((-1) * x57)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))))
  have u8 : (x01 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))))
  have h := NineTheoryTrial.th561 t x01 x03 x13 x15 x35 x36 x57
  exact (fun hh => (fun hh => hh) (hh (And.intro u5 (And.intro u4 (And.intro u8 (And.intro u7 (And.intro u1 (And.intro u6 (And.intro u2 (And.intro u0 u3)))))))))) h

theorem clause7967 (t x78 : ℝ) : ((¬ ((t + ((-1) * x78)) ≤ 0)) ∨ (t ≤ x78)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x78)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x78) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th563 t x78
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7969 (t x78 : ℝ) : ((¬ (t ≤ x78)) ∨ (¬ (x78 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x78 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th564 t x78
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause7971 (t x78 : ℝ) (h : (x78 < t)) : ((x78 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x78 < t) := fun hh => hn hh
  exact u0 h

theorem clause7972 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((x68 + ((-1) * x78)) ≥ 0) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 + ((-1) * x78)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7974 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7975 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((t + ((-1) * x67) + x68) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7983 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((x67 + ((-1) * x68)) ≥ 0) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7984 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7985 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x67) + x68) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7986 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x68) + x78) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x68) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7988 (t x67 x68 x78 : ℝ) : (((t + x67 + ((-1) * x68)) ≥ 1) ∨ ((x67 + ((-1) * x68)) ≥ 0) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x67 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7994 (t x67 x68 x78 : ℝ) : (((t + x68 + ((-1) * x78)) ≥ 1) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x67 ≤ x68)) ∨ (¬ (x68 ≤ x78)) ∨ (¬ ((x78 - x67) ≥ 1)) ∨ (¬ ((x68 - x67) ≤ (t - 1))) ∨ (¬ ((x78 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x68 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x78) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x78 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x68 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x78 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7997 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((x68 + ((-1) * x78)) ≥ 0) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 + ((-1) * x78)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause7999 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8000 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x68)) ≤ 0) ∨ ((t + ((-1) * x67) + x68) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8008 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((x67 + ((-1) * x68)) ≥ 0) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8009 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8010 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x67) + x68) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x67) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8011 (t x67 x68 x78 : ℝ) : (((x67 + ((-1) * x78)) ≤ (-1)) ∨ ((t + ((-1) * x68) + x78) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 + ((-1) * x78)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x68) + x78) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8013 (t x67 x68 x78 : ℝ) : (((t + x67 + ((-1) * x68)) ≥ 1) ∨ ((x67 + ((-1) * x68)) ≥ 0) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x67 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8019 (t x67 x68 x78 : ℝ) : (((t + x68 + ((-1) * x78)) ≥ 1) ∨ ((x67 + ((-1) * x78)) ≥ 1) ∨ (¬ (x78 ≤ x68)) ∨ (¬ (x68 ≤ x67)) ∨ (¬ ((x67 - x78) ≥ 1)) ∨ (¬ ((x67 - x68) ≤ (t - 1))) ∨ (¬ ((x68 - x78) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x68 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 + ((-1) * x78)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x78 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x68 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x78) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x67 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x78) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th567 t x67 x68 x78
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8072 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x67 ≤ x68) ∨ (x78 ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x68) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8073 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x67 ≤ x68) ∨ (x68 ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x67) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8074 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x67 ≤ x68) ∨ ((x67 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8075 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x67 ≤ x68) ∨ ((x67 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8076 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x67 ≤ x68) ∨ ((x68 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x67 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8077 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x68 ≤ x78) ∨ (x78 ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x68) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8078 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x68 ≤ x78) ∨ (x68 ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x67) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8079 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x68 ≤ x78) ∨ ((x67 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8080 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x68 ≤ x78) ∨ ((x67 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8081 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : ((x68 ≤ x78) ∨ ((x68 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 ≤ x78) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8082 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x67) ≥ 1) ∨ (x78 ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x67) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x68) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8083 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x67) ≥ 1) ∨ (x68 ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x67) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x67) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8084 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x67) ≥ 1) ∨ ((x67 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x67) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8085 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x67) ≥ 1) ∨ ((x67 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x67) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8086 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x67) ≥ 1) ∨ ((x68 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x67) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8087 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x68 - x67) ≤ (t - 1)) ∨ (x78 ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x67) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x68) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8088 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x68 - x67) ≤ (t - 1)) ∨ (x68 ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x67) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x67) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8089 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x68 - x67) ≤ (t - 1)) ∨ ((x67 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x67) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8090 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x68 - x67) ≤ (t - 1)) ∨ ((x67 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x67) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8091 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x68 - x67) ≤ (t - 1)) ∨ ((x68 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x67) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8092 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x68) ≤ (t - 1)) ∨ (x78 ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x68) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x78 ≤ x68) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8093 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x68) ≤ (t - 1)) ∨ (x68 ≤ x67)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x68) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x67) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8094 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x68) ≤ (t - 1)) ∨ ((x67 - x78) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x68) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x78) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8095 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x68) ≤ (t - 1)) ∨ ((x67 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x68) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x67 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8096 (t x67 x68 x78 : ℝ) (h : (((x67 ≤ x68) ∧ (x68 ≤ x78) ∧ ((x78 - x67) ≥ 1) ∧ ((x68 - x67) ≤ (t - 1)) ∧ ((x78 - x68) ≤ (t - 1))) ∨ ((x78 ≤ x68) ∧ (x68 ≤ x67) ∧ ((x67 - x78) ≥ 1) ∧ ((x67 - x68) ≤ (t - 1)) ∧ ((x68 - x78) ≤ (t - 1))))) : (((x78 - x68) ≤ (t - 1)) ∨ ((x68 - x78) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x78 - x68) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x68 - x78) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8097 (x02 x25 x27 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x27)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x27)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x25 + ((-1) * x27)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x27)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th569 x02 x25 x27
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause8100 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x02 + ((-1) * x07)) ≤ 0) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8105 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x07 + ((-1) * x27)) ≤ 0) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8108 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((x07 + ((-1) * x27)) ≥ 0) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8109 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((x02 + ((-1) * x07)) ≥ 0) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8110 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x02 + ((-1) * x27)) ≤ (-1)) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8111 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x07) ≥ 1) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x07) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8115 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((t + x02 + ((-1) * x07)) ≥ 1) ∨ (¬ (x02 ≤ x07)) ∨ (¬ (x07 ≤ x27)) ∨ (¬ ((x27 - x02) ≥ 1)) ∨ (¬ ((x07 - x02) ≤ (t - 1))) ∨ (¬ ((x27 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x27 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8125 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x02 + ((-1) * x07)) ≤ 0) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8130 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x07 + ((-1) * x27)) ≤ 0) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8133 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((x07 + ((-1) * x27)) ≥ 0) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8134 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((x02 + ((-1) * x07)) ≥ 0) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8135 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((x02 + ((-1) * x27)) ≤ (-1)) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8136 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x07) ≥ 1) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x07) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8140 (t x02 x07 x27 : ℝ) : (((x02 + ((-1) * x27)) ≥ 1) ∨ ((t + x02 + ((-1) * x07)) ≥ 1) ∨ (¬ (x27 ≤ x07)) ∨ (¬ (x07 ≤ x02)) ∨ (¬ ((x02 - x27) ≥ 1)) ∨ (¬ ((x02 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x27)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x07)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x27 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x27) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th571 t x02 x07 x27
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause8198 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x02 ≤ x07) ∨ (x27 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8199 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x02 ≤ x07) ∨ (x07 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8200 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x02 ≤ x07) ∨ ((x02 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8201 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x02 ≤ x07) ∨ ((x02 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8202 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x02 ≤ x07) ∨ ((x07 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8203 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x07 ≤ x27) ∨ (x27 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8204 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x07 ≤ x27) ∨ (x07 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8205 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x07 ≤ x27) ∨ ((x02 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8206 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x07 ≤ x27) ∨ ((x02 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8207 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : ((x07 ≤ x27) ∨ ((x07 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8208 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x02) ≥ 1) ∨ (x27 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8209 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x02) ≥ 1) ∨ (x07 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8210 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x02) ≥ 1) ∨ ((x02 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8211 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x02) ≥ 1) ∨ ((x02 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8212 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x02) ≥ 1) ∨ ((x07 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8213 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x07 - x02) ≤ (t - 1)) ∨ (x27 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8214 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x07 - x02) ≤ (t - 1)) ∨ (x07 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8215 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x07 - x02) ≤ (t - 1)) ∨ ((x02 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8216 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x07 - x02) ≤ (t - 1)) ∨ ((x02 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause8217 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x07 - x02) ≤ (t - 1)) ∨ ((x07 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause8218 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x07) ≤ (t - 1)) ∨ (x27 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause8219 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x07) ≤ (t - 1)) ∨ (x07 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause8220 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x07) ≤ (t - 1)) ∨ ((x02 - x27) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x27) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause8221 (t x02 x07 x27 : ℝ) (h : (((x02 ≤ x07) ∧ (x07 ≤ x27) ∧ ((x27 - x02) ≥ 1) ∧ ((x07 - x02) ≤ (t - 1)) ∧ ((x27 - x07) ≤ (t - 1))) ∨ ((x27 ≤ x07) ∧ (x07 ≤ x02) ∧ ((x02 - x27) ≥ 1) ∧ ((x02 - x07) ≤ (t - 1)) ∧ ((x07 - x27) ≤ (t - 1))))) : (((x27 - x07) ≤ (t - 1)) ∨ ((x02 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

#print axioms clause8221
end NineCNFDirectTrial
