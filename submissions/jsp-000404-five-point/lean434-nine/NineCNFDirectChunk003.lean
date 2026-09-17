import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause4055 (t x05 x06 x56 : ℝ) : (((x06 + ((-1) * x56)) ≤ 0) ∨ ((x05 + ((-1) * x06)) ≥ 0) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4056 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x06 + ((-1) * x56)) ≤ 0) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4058 (t x05 x06 x56 : ℝ) : (((x06 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x06) + x56) ≥ 1) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4059 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≤ (-1)) ∨ ((x06 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4060 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x06)) ≥ 0) ∨ ((x05 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4061 (t x05 x06 x56 : ℝ) : (((x05 + ((-1) * x56)) ≥ 1) ∨ ((x05 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x56 ≤ x06)) ∨ (¬ (x06 ≤ x05)) ∨ (¬ ((x05 - x56) ≥ 1)) ∨ (¬ ((x05 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
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
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4124 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x05 ≤ x06) ∨ (x56 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4125 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x05 ≤ x06) ∨ (x06 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4126 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x05 ≤ x06) ∨ ((x05 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4127 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x05 ≤ x06) ∨ ((x05 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4128 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x05 ≤ x06) ∨ ((x06 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4129 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x06 ≤ x56) ∨ (x56 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4130 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x06 ≤ x56) ∨ (x06 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4131 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x06 ≤ x56) ∨ ((x05 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4132 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x06 ≤ x56) ∨ ((x05 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4133 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : ((x06 ≤ x56) ∨ ((x06 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4134 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x05) ≥ 1) ∨ (x56 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4135 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x05) ≥ 1) ∨ (x06 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4136 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x05) ≥ 1) ∨ ((x05 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4137 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x05) ≥ 1) ∨ ((x05 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4138 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x05) ≥ 1) ∨ ((x06 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4139 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x06 - x05) ≤ (t - 1)) ∨ (x56 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4140 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x06 - x05) ≤ (t - 1)) ∨ (x06 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4141 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x06 - x05) ≤ (t - 1)) ∨ ((x05 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4142 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x06 - x05) ≤ (t - 1)) ∨ ((x05 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4143 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x06 - x05) ≤ (t - 1)) ∨ ((x06 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4144 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x06) ≤ (t - 1)) ∨ (x56 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4145 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x06) ≤ (t - 1)) ∨ (x06 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4146 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x06) ≤ (t - 1)) ∨ ((x05 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4147 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x06) ≤ (t - 1)) ∨ ((x05 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4148 (t x05 x06 x56 : ℝ) (h : (((x05 ≤ x06) ∧ (x06 ≤ x56) ∧ ((x56 - x05) ≥ 1) ∧ ((x06 - x05) ≤ (t - 1)) ∧ ((x56 - x06) ≤ (t - 1))) ∨ ((x56 ≤ x06) ∧ (x06 ≤ x05) ∧ ((x05 - x56) ≥ 1) ∧ ((x05 - x06) ≤ (t - 1)) ∧ ((x06 - x56) ≤ (t - 1))))) : (((x56 - x06) ≤ (t - 1)) ∨ ((x06 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4149 (x05 x35 x56 : ℝ) : ((¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x05 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th232 x05 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause4150 (t x05 x06 x36 x45 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x05 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x36 + ((-1) * x56)) ≥ 0)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x45 + ((-1) * x58)) ≤ (-1))) ∨ (¬ ((t + x56 + ((-1) * x58)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x05 + ((-1) * x45)) ≤ 0) := by
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
  have u4 : ((x36 + ((-1) * x56)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((t + x56 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th233 t x05 x06 x36 x45 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u5 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u6 (And.intro u2 u7))))))))) h

theorem clause4151 (t x58 : ℝ) : ((¬ ((t + ((-1) * x58)) ≤ 0)) ∨ (t ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x58)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x58) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th235 t x58
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4153 (t x58 : ℝ) : ((¬ (t ≤ x58)) ∨ (¬ (x58 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x58 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th236 t x58
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4155 (t x58 : ℝ) (h : (x58 < t)) : ((x58 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 < t) := fun hh => hn hh
  exact u0 h

theorem clause4163 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((x58 + ((-1) * x68)) ≤ 0) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4166 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((x58 + ((-1) * x68)) ≥ 0) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4167 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((x56 + ((-1) * x58)) ≥ 0) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4168 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((x56 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4169 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x56) + x58) ≥ 1) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56) + x58) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4170 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x58) + x68) ≥ 1) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4172 (t x56 x58 x68 : ℝ) : (((t + x56 + ((-1) * x58)) ≥ 1) ∨ ((x56 + ((-1) * x58)) ≥ 0) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x56 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4173 (t x56 x58 x68 : ℝ) : (((t + x56 + ((-1) * x58)) ≥ 1) ∨ ((x56 + ((-1) * x68)) ≥ 1) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x56 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4176 (t x56 x58 x68 : ℝ) : (((t + x58 + ((-1) * x68)) ≥ 1) ∨ ((x58 + ((-1) * x68)) ≥ 0) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x58 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4178 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((t + x58 + ((-1) * x68)) ≥ 1) ∨ (¬ (x56 ≤ x58)) ∨ (¬ (x58 ≤ x68)) ∨ (¬ ((x68 - x56) ≥ 1)) ∨ (¬ ((x58 - x56) ≤ (t - 1))) ∨ (¬ ((x68 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x58 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x58 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4188 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((x58 + ((-1) * x68)) ≤ 0) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4191 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((x58 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4192 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((x56 + ((-1) * x58)) ≥ 0) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4193 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((x56 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4194 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x56) + x58) ≥ 1) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x56) + x58) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4195 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x58) + x68) ≥ 1) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x58) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4197 (t x56 x58 x68 : ℝ) : (((t + x56 + ((-1) * x58)) ≥ 1) ∨ ((x56 + ((-1) * x58)) ≥ 0) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x56 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4198 (t x56 x58 x68 : ℝ) : (((t + x56 + ((-1) * x58)) ≥ 1) ∨ ((x56 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x56 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4201 (t x56 x58 x68 : ℝ) : (((t + x58 + ((-1) * x68)) ≥ 1) ∨ ((x58 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x58 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4203 (t x56 x58 x68 : ℝ) : (((x56 + ((-1) * x68)) ≥ 1) ∨ ((t + x58 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x58)) ∨ (¬ (x58 ≤ x56)) ∨ (¬ ((x56 - x68) ≥ 1)) ∨ (¬ ((x56 - x58) ≤ (t - 1))) ∨ (¬ ((x58 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x58 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x58 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x56 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th239 t x56 x58 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4256 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x56 ≤ x58) ∨ (x68 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4257 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x56 ≤ x58) ∨ (x58 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4258 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x56 ≤ x58) ∨ ((x56 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4259 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x56 ≤ x58) ∨ ((x56 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4260 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x56 ≤ x58) ∨ ((x58 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4261 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x58 ≤ x68) ∨ (x68 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4262 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x58 ≤ x68) ∨ (x58 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4263 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x58 ≤ x68) ∨ ((x56 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4264 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x58 ≤ x68) ∨ ((x56 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4265 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : ((x58 ≤ x68) ∨ ((x58 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x58 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4266 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x56) ≥ 1) ∨ (x68 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4267 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x56) ≥ 1) ∨ (x58 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4268 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x56) ≥ 1) ∨ ((x56 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4269 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x56) ≥ 1) ∨ ((x56 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4270 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x56) ≥ 1) ∨ ((x58 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x56) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4271 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x58 - x56) ≤ (t - 1)) ∨ (x68 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4272 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x58 - x56) ≤ (t - 1)) ∨ (x58 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4273 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x58 - x56) ≤ (t - 1)) ∨ ((x56 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4274 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x58 - x56) ≤ (t - 1)) ∨ ((x56 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4275 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x58 - x56) ≤ (t - 1)) ∨ ((x58 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x56) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4276 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x58) ≤ (t - 1)) ∨ (x68 ≤ x58)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x58) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4277 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x58) ≤ (t - 1)) ∨ (x58 ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x56) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4278 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x58) ≤ (t - 1)) ∨ ((x56 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4279 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x58) ≤ (t - 1)) ∨ ((x56 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x56 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4280 (t x56 x58 x68 : ℝ) (h : (((x56 ≤ x58) ∧ (x58 ≤ x68) ∧ ((x68 - x56) ≥ 1) ∧ ((x58 - x56) ≤ (t - 1)) ∧ ((x68 - x58) ≤ (t - 1))) ∨ ((x68 ≤ x58) ∧ (x58 ≤ x56) ∧ ((x56 - x68) ≥ 1) ∧ ((x56 - x58) ≤ (t - 1)) ∧ ((x58 - x68) ≤ (t - 1))))) : (((x68 - x58) ≤ (t - 1)) ∨ ((x58 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x58) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x58 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4288 (t x45 x48 x58 : ℝ) : (((x48 + ((-1) * x58)) ≤ 0) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4291 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((x48 + ((-1) * x58)) ≥ 0) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4293 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4294 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((t + ((-1) * x45) + x48) ≥ 1) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4295 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x58) ≥ 1) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x58) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4298 (t x45 x48 x58 : ℝ) : (((t + x45 + ((-1) * x48)) ≥ 1) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x45 ≤ x48)) ∨ (¬ (x48 ≤ x58)) ∨ (¬ ((x58 - x45) ≥ 1)) ∨ (¬ ((x48 - x45) ≤ (t - 1))) ∨ (¬ ((x58 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4313 (t x45 x48 x58 : ℝ) : (((x48 + ((-1) * x58)) ≤ 0) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 + ((-1) * x58)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4316 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((x48 + ((-1) * x58)) ≥ 0) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x58)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4318 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4319 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((t + ((-1) * x45) + x48) ≥ 1) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4320 (t x45 x48 x58 : ℝ) : (((x45 + ((-1) * x58)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x58) ≥ 1) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x58) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4323 (t x45 x48 x58 : ℝ) : (((t + x45 + ((-1) * x48)) ≥ 1) ∨ ((x45 + ((-1) * x58)) ≥ 1) ∨ (¬ (x58 ≤ x48)) ∨ (¬ (x48 ≤ x45)) ∨ (¬ ((x45 - x58) ≥ 1)) ∨ (¬ ((x45 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th242 t x45 x48 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4381 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x45 ≤ x48) ∨ (x58 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4382 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x45 ≤ x48) ∨ (x48 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4383 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x45 ≤ x48) ∨ ((x45 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4384 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x45 ≤ x48) ∨ ((x45 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4385 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x45 ≤ x48) ∨ ((x48 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4386 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x48 ≤ x58) ∨ (x58 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4387 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x48 ≤ x58) ∨ (x48 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4388 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x48 ≤ x58) ∨ ((x45 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4389 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x48 ≤ x58) ∨ ((x45 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4390 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : ((x48 ≤ x58) ∨ ((x48 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4391 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x45) ≥ 1) ∨ (x58 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4392 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x45) ≥ 1) ∨ (x48 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4393 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x45) ≥ 1) ∨ ((x45 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4394 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x45) ≥ 1) ∨ ((x45 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4395 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x45) ≥ 1) ∨ ((x48 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4396 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x48 - x45) ≤ (t - 1)) ∨ (x58 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4397 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x48 - x45) ≤ (t - 1)) ∨ (x48 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4398 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x48 - x45) ≤ (t - 1)) ∨ ((x45 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4399 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x48 - x45) ≤ (t - 1)) ∨ ((x45 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4400 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x48 - x45) ≤ (t - 1)) ∨ ((x48 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4401 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x48) ≤ (t - 1)) ∨ (x58 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4402 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x48) ≤ (t - 1)) ∨ (x48 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4403 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x48) ≤ (t - 1)) ∨ ((x45 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4404 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x48) ≤ (t - 1)) ∨ ((x45 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4405 (t x45 x48 x58 : ℝ) (h : (((x45 ≤ x48) ∧ (x48 ≤ x58) ∧ ((x58 - x45) ≥ 1) ∧ ((x48 - x45) ≤ (t - 1)) ∧ ((x58 - x48) ≤ (t - 1))) ∨ ((x58 ≤ x48) ∧ (x48 ≤ x45) ∧ ((x45 - x58) ≥ 1) ∧ ((x45 - x48) ≤ (t - 1)) ∧ ((x48 - x58) ≤ (t - 1))))) : (((x58 - x48) ≤ (t - 1)) ∨ ((x48 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4406 (t x05 x06 x45 x56 x58 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x06)) ≥ 0)) ∨ ((t + ((-1) * x45)) ≤ 0) ∨ (¬ ((x45 + ((-1) * x58)) ≥ 1)) ∨ (¬ ((x05 + ((-1) * x58)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 + ((-1) * x58)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x05 + ((-1) * x58)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th244 t x05 x06 x45 x56 x58 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u7 (And.intro u3 (And.intro u1 (And.intro u0 u5))))))))) h

theorem clause4419 (t x05 x08 x58 : ℝ) : (((x05 + ((-1) * x58)) ≥ 1) ∨ ((x05 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x05 ≤ x08)) ∨ (¬ (x08 ≤ x58)) ∨ (¬ ((x58 - x05) ≥ 1)) ∨ (¬ ((x08 - x05) ≤ (t - 1))) ∨ (¬ ((x58 - x08) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x05 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x58) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x58 - x05) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x08 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x58 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th246 t x05 x08 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4444 (t x05 x08 x58 : ℝ) : (((x05 + ((-1) * x58)) ≥ 1) ∨ ((x05 + ((-1) * x58)) ≤ (-1)) ∨ (¬ (x58 ≤ x08)) ∨ (¬ (x08 ≤ x05)) ∨ (¬ ((x05 - x58) ≥ 1)) ∨ (¬ ((x05 - x08) ≤ (t - 1))) ∨ (¬ ((x08 - x58) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x58)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x58)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x58 ≤ x08) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x08 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x05 - x58) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x08) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x08 - x58) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th246 t x05 x08 x58
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4507 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x05 ≤ x08) ∨ (x58 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4508 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x05 ≤ x08) ∨ (x08 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4509 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x05 ≤ x08) ∨ ((x05 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4510 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x05 ≤ x08) ∨ ((x05 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4511 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x05 ≤ x08) ∨ ((x08 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x08) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4512 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x08 ≤ x58) ∨ (x58 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4513 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x08 ≤ x58) ∨ (x08 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4514 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x08 ≤ x58) ∨ ((x05 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4515 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x08 ≤ x58) ∨ ((x05 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4516 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : ((x08 ≤ x58) ∨ ((x08 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x08 ≤ x58) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4517 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x05) ≥ 1) ∨ (x58 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4518 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x05) ≥ 1) ∨ (x08 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4519 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x05) ≥ 1) ∨ ((x05 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4520 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x05) ≥ 1) ∨ ((x05 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4521 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x05) ≥ 1) ∨ ((x08 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x05) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4522 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x08 - x05) ≤ (t - 1)) ∨ (x58 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4523 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x08 - x05) ≤ (t - 1)) ∨ (x08 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4524 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x08 - x05) ≤ (t - 1)) ∨ ((x05 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4525 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x08 - x05) ≤ (t - 1)) ∨ ((x05 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4526 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x08 - x05) ≤ (t - 1)) ∨ ((x08 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x08 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4527 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x08) ≤ (t - 1)) ∨ (x58 ≤ x08)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x58 ≤ x08) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4528 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x08) ≤ (t - 1)) ∨ (x08 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x08 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4529 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x08) ≤ (t - 1)) ∨ ((x05 - x58) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x58) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4530 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x08) ≤ (t - 1)) ∨ ((x05 - x08) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x08) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4531 (t x05 x08 x58 : ℝ) (h : (((x05 ≤ x08) ∧ (x08 ≤ x58) ∧ ((x58 - x05) ≥ 1) ∧ ((x08 - x05) ≤ (t - 1)) ∧ ((x58 - x08) ≤ (t - 1))) ∨ ((x58 ≤ x08) ∧ (x08 ≤ x05) ∧ ((x05 - x58) ≥ 1) ∧ ((x05 - x08) ≤ (t - 1)) ∧ ((x08 - x58) ≤ (t - 1))))) : (((x58 - x08) ≤ (t - 1)) ∨ ((x08 - x58) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x58 - x08) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x08 - x58) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4532 (t x02 x23 x26 x34 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ ((t + ((-1) * x23)) ≤ 0) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ (x34 ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : (x34 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th248 t x02 x23 x26 x34 x36 x67
  exact (fun hh => (fun hh => hh u7) (hh (And.intro u2 (And.intro u1 (And.intro u0 (And.intro u5 (And.intro u6 (And.intro u3 u4)))))))) h

theorem clause4533 (t x01 x02 x14 x26 x36 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th249 t x01 x02 x14 x26 x36 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u4 (And.intro u0 (And.intro u7 (And.intro u3 (And.intro u2 (And.intro u5 u1))))))))) h

theorem clause4534 (t x01 x02 x12 : ℝ) : ((¬ ((x01 + ((-1) * x12)) ≥ 1)) ∨ ((t + x01 + ((-1) * x02)) ≥ 1) ∨ ((t + ((-1) * x02)) ≤ 0) ∨ (¬ (x12 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x12)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x02)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x12 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th250 t x01 x02 x12
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause4535 (x12 : ℝ) (h : (x12 ≥ 0)) : ((x12 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause4536 (t x02 : ℝ) : ((¬ ((t + ((-1) * x02)) ≤ 0)) ∨ (t ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x02)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x02) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th252 t x02
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4538 (t x02 : ℝ) : ((¬ (t ≤ x02)) ∨ (¬ (x02 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x02 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th253 t x02
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4540 (t x02 : ℝ) (h : (x02 < t)) : ((x02 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 < t) := fun hh => hn hh
  exact u0 h

theorem clause4541 (x02 x23 x26 : ℝ) : ((¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((x02 + ((-1) * x26)) ≥ 1) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th255 x02 x23 x26
  exact (fun hh => u1 (hh (And.intro u0 u2))) h

theorem clause4542 (t x03 x06 x23 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x03) + x23) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x23 + ((-1) * x36)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + ((-1) * x03) + x23) ≥ 1) := by
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
  have u4 : ((x03 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th256 t x03 x06 x23 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u2 (And.intro u3 (And.intro u1 u0))))))) h

theorem clause4543 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≤ 0) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4545 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x23 + ((-1) * x26)) ≤ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4549 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((x26 + ((-1) * x36)) ≤ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4550 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x26 + ((-1) * x36)) ≤ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4552 (t x23 x26 x36 : ℝ) : (((x26 + ((-1) * x36)) ≤ 0) ∨ ((t + ((-1) * x26) + x36) ≥ 1) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4553 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≤ (-1)) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4554 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4555 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4556 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≤ (-1)) ∨ ((t + ((-1) * x23) + x26) ≥ 1) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4557 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≤ (-1)) ∨ ((t + ((-1) * x26) + x36) ≥ 1) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4559 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((t + x23 + ((-1) * x26)) ≥ 1) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4563 (t x23 x26 x36 : ℝ) : (((t + x26 + ((-1) * x36)) ≥ 1) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x26 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4565 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((t + x26 + ((-1) * x36)) ≥ 1) ∨ (¬ (x23 ≤ x26)) ∨ (¬ (x26 ≤ x36)) ∨ (¬ ((x36 - x23) ≥ 1)) ∨ (¬ ((x26 - x23) ≤ (t - 1))) ∨ (¬ ((x36 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x26 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x23) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x23) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4568 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≤ 0) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4570 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x23 + ((-1) * x26)) ≤ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4574 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((x26 + ((-1) * x36)) ≤ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4575 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x26 + ((-1) * x36)) ≤ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4577 (t x23 x26 x36 : ℝ) : (((x26 + ((-1) * x36)) ≤ 0) ∨ ((t + ((-1) * x26) + x36) ≥ 1) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4578 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≤ (-1)) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4579 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4580 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((x23 + ((-1) * x36)) ≤ (-1)) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4581 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≤ (-1)) ∨ ((t + ((-1) * x23) + x26) ≥ 1) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4584 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x26)) ≥ 0) ∨ ((t + x23 + ((-1) * x26)) ≥ 1) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4585 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((t + x23 + ((-1) * x26)) ≥ 1) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x23 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4588 (t x23 x26 x36 : ℝ) : (((t + x26 + ((-1) * x36)) ≥ 1) ∨ ((x26 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x26 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4590 (t x23 x26 x36 : ℝ) : (((x23 + ((-1) * x36)) ≥ 1) ∨ ((t + x26 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x26)) ∨ (¬ (x26 ≤ x23)) ∨ (¬ ((x23 - x36) ≥ 1)) ∨ (¬ ((x23 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x23 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x26 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x23) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x23 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x23 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th258 t x23 x26 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4643 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x23 ≤ x26) ∨ (x36 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4644 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x23 ≤ x26) ∨ (x26 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4645 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x23 ≤ x26) ∨ ((x23 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4646 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x23 ≤ x26) ∨ ((x23 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4647 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x23 ≤ x26) ∨ ((x26 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x23 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4648 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x26 ≤ x36) ∨ (x36 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4649 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x26 ≤ x36) ∨ (x26 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4650 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x26 ≤ x36) ∨ ((x23 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4651 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x26 ≤ x36) ∨ ((x23 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4652 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : ((x26 ≤ x36) ∨ ((x26 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4653 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x23) ≥ 1) ∨ (x36 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4654 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x23) ≥ 1) ∨ (x26 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4655 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x23) ≥ 1) ∨ ((x23 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4656 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x23) ≥ 1) ∨ ((x23 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4657 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x23) ≥ 1) ∨ ((x26 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x23) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4658 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x26 - x23) ≤ (t - 1)) ∨ (x36 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4659 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x26 - x23) ≤ (t - 1)) ∨ (x26 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4660 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x26 - x23) ≤ (t - 1)) ∨ ((x23 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4661 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x26 - x23) ≤ (t - 1)) ∨ ((x23 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4662 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x26 - x23) ≤ (t - 1)) ∨ ((x26 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x23) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4663 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x26) ≤ (t - 1)) ∨ (x36 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4664 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x26) ≤ (t - 1)) ∨ (x26 ≤ x23)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x23) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4665 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x26) ≤ (t - 1)) ∨ ((x23 - x36) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x36) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4666 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x26) ≤ (t - 1)) ∨ ((x23 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x23 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4667 (t x23 x26 x36 : ℝ) (h : (((x23 ≤ x26) ∧ (x26 ≤ x36) ∧ ((x36 - x23) ≥ 1) ∧ ((x26 - x23) ≤ (t - 1)) ∧ ((x36 - x26) ≤ (t - 1))) ∨ ((x36 ≤ x26) ∧ (x26 ≤ x23) ∧ ((x23 - x36) ≥ 1) ∧ ((x23 - x26) ≤ (t - 1)) ∧ ((x26 - x36) ≤ (t - 1))))) : (((x36 - x26) ≤ (t - 1)) ∨ ((x26 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4668 (x02 x23 x26 : ℝ) : ((¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x26)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x23 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th260 x02 x23 x26
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause4671 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x02 + ((-1) * x06)) ≤ 0) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4672 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x06)) ≤ 0) ∨ ((t + ((-1) * x02) + x06) ≥ 1) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4676 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x06 + ((-1) * x26)) ≤ 0) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4679 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((x06 + ((-1) * x26)) ≥ 0) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4680 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((x02 + ((-1) * x06)) ≥ 0) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4681 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x02 + ((-1) * x26)) ≤ (-1)) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4682 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x06) ≥ 1) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4683 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x26) ≥ 1) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4686 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((t + x02 + ((-1) * x06)) ≥ 1) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x06)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4691 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((t + x06 + ((-1) * x26)) ≥ 1) ∨ (¬ (x02 ≤ x06)) ∨ (¬ (x06 ≤ x26)) ∨ (¬ ((x26 - x02) ≥ 1)) ∨ (¬ ((x06 - x02) ≤ (t - 1))) ∨ (¬ ((x26 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x06 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4696 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x02 + ((-1) * x06)) ≤ 0) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4697 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x06)) ≤ 0) ∨ ((t + ((-1) * x02) + x06) ≥ 1) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4700 (t x02 x06 x26 : ℝ) : (((x06 + ((-1) * x26)) ≤ 0) ∨ ((x02 + ((-1) * x06)) ≥ 0) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4701 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x06 + ((-1) * x26)) ≤ 0) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4704 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((x06 + ((-1) * x26)) ≥ 0) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4705 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((x02 + ((-1) * x06)) ≥ 0) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4706 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((x02 + ((-1) * x26)) ≤ (-1)) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4707 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x06) ≥ 1) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x06) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4708 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x26) ≥ 1) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4711 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((t + x02 + ((-1) * x06)) ≥ 1) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x02 + ((-1) * x06)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4716 (t x02 x06 x26 : ℝ) : (((x02 + ((-1) * x26)) ≥ 1) ∨ ((t + x06 + ((-1) * x26)) ≥ 1) ∨ (¬ (x26 ≤ x06)) ∨ (¬ (x06 ≤ x02)) ∨ (¬ ((x02 - x26) ≥ 1)) ∨ (¬ ((x02 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x06 + ((-1) * x26)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th262 t x02 x06 x26
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4769 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x02 ≤ x06) ∨ (x26 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4770 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x02 ≤ x06) ∨ (x06 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4771 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x02 ≤ x06) ∨ ((x02 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4772 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x02 ≤ x06) ∨ ((x02 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4773 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x02 ≤ x06) ∨ ((x06 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4774 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x06 ≤ x26) ∨ (x26 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4775 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x06 ≤ x26) ∨ (x06 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4776 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x06 ≤ x26) ∨ ((x02 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4777 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x06 ≤ x26) ∨ ((x02 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4778 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : ((x06 ≤ x26) ∨ ((x06 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4779 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x02) ≥ 1) ∨ (x26 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4780 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x02) ≥ 1) ∨ (x06 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4781 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x02) ≥ 1) ∨ ((x02 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4782 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x02) ≥ 1) ∨ ((x02 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4783 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x02) ≥ 1) ∨ ((x06 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4784 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x06 - x02) ≤ (t - 1)) ∨ (x26 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4785 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x06 - x02) ≤ (t - 1)) ∨ (x06 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4786 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x06 - x02) ≤ (t - 1)) ∨ ((x02 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4787 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x06 - x02) ≤ (t - 1)) ∨ ((x02 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4788 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x06 - x02) ≤ (t - 1)) ∨ ((x06 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4789 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x06) ≤ (t - 1)) ∨ (x26 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4790 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x06) ≤ (t - 1)) ∨ (x06 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4791 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x06) ≤ (t - 1)) ∨ ((x02 - x26) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x26) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4792 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x06) ≤ (t - 1)) ∨ ((x02 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4793 (t x02 x06 x26 : ℝ) (h : (((x02 ≤ x06) ∧ (x06 ≤ x26) ∧ ((x26 - x02) ≥ 1) ∧ ((x06 - x02) ≤ (t - 1)) ∧ ((x26 - x06) ≤ (t - 1))) ∨ ((x26 ≤ x06) ∧ (x06 ≤ x02) ∧ ((x02 - x26) ≥ 1) ∧ ((x02 - x06) ≤ (t - 1)) ∧ ((x06 - x26) ≤ (t - 1))))) : (((x26 - x06) ≤ (t - 1)) ∨ ((x06 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4795 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≥ 0) ∨ ((x25 + ((-1) * x26)) ≤ 0) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4797 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x26)) ≤ 0) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4802 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≤ 0) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4804 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x26) + x56) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4805 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≥ 0) ∨ ((x25 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4806 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((x25 + ((-1) * x26)) ≥ 0) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4807 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4809 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x26) + x56) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4817 (t x25 x26 x56 : ℝ) : (((t + x26 + ((-1) * x56)) ≥ 1) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x25 ≤ x26)) ∨ (¬ (x26 ≤ x56)) ∨ (¬ ((x56 - x25) ≥ 1)) ∨ (¬ ((x26 - x25) ≤ (t - 1))) ∨ (¬ ((x56 - x26) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x26 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4820 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≥ 0) ∨ ((x25 + ((-1) * x26)) ≤ 0) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4822 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x26)) ≤ 0) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x26)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4826 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≤ 0) ∨ ((x25 + ((-1) * x26)) ≥ 0) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4827 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≤ 0) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4829 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x26) + x56) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4830 (t x25 x26 x56 : ℝ) : (((x26 + ((-1) * x56)) ≥ 0) ∨ ((x25 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4831 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((x25 + ((-1) * x26)) ≥ 0) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x26)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4832 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4834 (t x25 x26 x56 : ℝ) : (((x25 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x26) + x56) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x26) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4842 (t x25 x26 x56 : ℝ) : (((t + x26 + ((-1) * x56)) ≥ 1) ∨ ((x25 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x26)) ∨ (¬ (x26 ≤ x25)) ∨ (¬ ((x25 - x56) ≥ 1)) ∨ (¬ ((x25 - x26) ≤ (t - 1))) ∨ (¬ ((x26 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x26 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th266 t x25 x26 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4895 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x25 ≤ x26) ∨ (x56 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4896 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x25 ≤ x26) ∨ (x26 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4897 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x25 ≤ x26) ∨ ((x25 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4898 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x25 ≤ x26) ∨ ((x25 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4899 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x25 ≤ x26) ∨ ((x26 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x26) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4900 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x26 ≤ x56) ∨ (x56 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4901 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x26 ≤ x56) ∨ (x26 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4902 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x26 ≤ x56) ∨ ((x25 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4903 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x26 ≤ x56) ∨ ((x25 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4904 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : ((x26 ≤ x56) ∨ ((x26 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4905 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x25) ≥ 1) ∨ (x56 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4906 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x25) ≥ 1) ∨ (x26 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4907 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x25) ≥ 1) ∨ ((x25 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4908 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x25) ≥ 1) ∨ ((x25 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4909 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x25) ≥ 1) ∨ ((x26 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4910 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x26 - x25) ≤ (t - 1)) ∨ (x56 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4911 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x26 - x25) ≤ (t - 1)) ∨ (x26 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4912 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x26 - x25) ≤ (t - 1)) ∨ ((x25 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4913 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x26 - x25) ≤ (t - 1)) ∨ ((x25 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4914 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x26 - x25) ≤ (t - 1)) ∨ ((x26 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4915 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x26) ≤ (t - 1)) ∨ (x56 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause4916 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x26) ≤ (t - 1)) ∨ (x26 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x26 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause4917 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x26) ≤ (t - 1)) ∨ ((x25 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause4918 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x26) ≤ (t - 1)) ∨ ((x25 - x26) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x26) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause4919 (t x25 x26 x56 : ℝ) (h : (((x25 ≤ x26) ∧ (x26 ≤ x56) ∧ ((x56 - x25) ≥ 1) ∧ ((x26 - x25) ≤ (t - 1)) ∧ ((x56 - x26) ≤ (t - 1))) ∨ ((x56 ≤ x26) ∧ (x26 ≤ x25) ∧ ((x25 - x56) ≥ 1) ∧ ((x25 - x26) ≤ (t - 1)) ∧ ((x26 - x56) ≤ (t - 1))))) : (((x56 - x26) ≤ (t - 1)) ∨ ((x26 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause4920 (t x06 : ℝ) : ((¬ ((t + ((-1) * x06)) ≤ 0)) ∨ (t ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x06) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th270 t x06
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4922 (t x06 : ℝ) : ((¬ (t ≤ x06)) ∨ (¬ (x06 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x06 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th271 t x06
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause4924 (t x06 : ℝ) (h : (x06 < t)) : ((x06 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 < t) := fun hh => hn hh
  exact u0 h

theorem clause4925 (t x01 x03 x14 x23 x35 x36 x46 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x03)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((t + x36 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x23 + ((-1) * x36)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
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
  have u3 : ((x23 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x36 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x23 + ((-1) * x36)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th273 t x01 x03 x14 x23 x35 x36 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u2 (And.intro u6 (And.intro u1 (And.intro u7 (And.intro u4 (And.intro u5 u0))))))))) h

theorem clause4926 (t x01 x02 x14 x26 x46 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x56 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x56 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x26 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x02 + ((-1) * x26)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th274 t x01 x02 x14 x26 x46 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u7 (And.intro u4 (And.intro u2 (And.intro u0 (And.intro u1 (And.intro u5 u6))))))))) h

theorem clause4927 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4929 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x26 + ((-1) * x27)) ≤ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4934 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x27 + ((-1) * x67)) ≤ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4937 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4938 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((x26 + ((-1) * x27)) ≥ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4939 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x26 + ((-1) * x67)) ≤ (-1)) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4941 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x67) ≥ 1) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4947 (t x26 x27 x67 : ℝ) : (((t + x27 + ((-1) * x67)) ≥ 1) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x27 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4949 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((t + x27 + ((-1) * x67)) ≥ 1) ∨ (¬ (x26 ≤ x27)) ∨ (¬ (x27 ≤ x67)) ∨ (¬ ((x67 - x26) ≥ 1)) ∨ (¬ ((x27 - x26) ≤ (t - 1))) ∨ (¬ ((x67 - x27) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x26 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x27 - x26) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4952 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x27)) ≤ 0) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4954 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x26 + ((-1) * x27)) ≤ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x27)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4958 (t x26 x27 x67 : ℝ) : (((x27 + ((-1) * x67)) ≤ 0) ∨ ((x26 + ((-1) * x27)) ≥ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4959 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x27 + ((-1) * x67)) ≤ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4962 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4963 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((x26 + ((-1) * x27)) ≥ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x27)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4964 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((x26 + ((-1) * x67)) ≤ (-1)) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4966 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x27) + x67) ≥ 1) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x27) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4972 (t x26 x27 x67 : ℝ) : (((t + x27 + ((-1) * x67)) ≥ 1) ∨ ((x27 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x27 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause4974 (t x26 x27 x67 : ℝ) : (((x26 + ((-1) * x67)) ≥ 1) ∨ ((t + x27 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x27)) ∨ (¬ (x27 ≤ x26)) ∨ (¬ ((x26 - x67) ≥ 1)) ∨ (¬ ((x26 - x27) ≤ (t - 1))) ∨ (¬ ((x27 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x26 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x27 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x27) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x27 ≤ x26) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x26 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 - x27) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x27 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th276 t x26 x27 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5027 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x26 ≤ x27) ∨ (x67 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5028 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x26 ≤ x27) ∨ (x27 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5029 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x26 ≤ x27) ∨ ((x26 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5030 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x26 ≤ x27) ∨ ((x26 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5031 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x26 ≤ x27) ∨ ((x27 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≤ x27) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5032 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x27 ≤ x67) ∨ (x67 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5033 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x27 ≤ x67) ∨ (x27 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5034 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x27 ≤ x67) ∨ ((x26 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5035 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x27 ≤ x67) ∨ ((x26 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5036 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : ((x27 ≤ x67) ∨ ((x27 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x27 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5037 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x26) ≥ 1) ∨ (x67 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5038 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x26) ≥ 1) ∨ (x27 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5039 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x26) ≥ 1) ∨ ((x26 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5040 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x26) ≥ 1) ∨ ((x26 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5041 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x26) ≥ 1) ∨ ((x27 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x26) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5042 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x27 - x26) ≤ (t - 1)) ∨ (x67 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5043 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x27 - x26) ≤ (t - 1)) ∨ (x27 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5044 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x27 - x26) ≤ (t - 1)) ∨ ((x26 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5045 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x27 - x26) ≤ (t - 1)) ∨ ((x26 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5046 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x27 - x26) ≤ (t - 1)) ∨ ((x27 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x27 - x26) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5047 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x27) ≤ (t - 1)) ∨ (x67 ≤ x27)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x27) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5048 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x27) ≤ (t - 1)) ∨ (x27 ≤ x26)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x27 ≤ x26) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5049 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x27) ≤ (t - 1)) ∨ ((x26 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5050 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x27) ≤ (t - 1)) ∨ ((x26 - x27) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x26 - x27) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5051 (t x26 x27 x67 : ℝ) (h : (((x26 ≤ x27) ∧ (x27 ≤ x67) ∧ ((x67 - x26) ≥ 1) ∧ ((x27 - x26) ≤ (t - 1)) ∧ ((x67 - x27) ≤ (t - 1))) ∨ ((x67 ≤ x27) ∧ (x27 ≤ x26) ∧ ((x26 - x67) ≥ 1) ∧ ((x26 - x27) ≤ (t - 1)) ∧ ((x27 - x67) ≤ (t - 1))))) : (((x67 - x27) ≤ (t - 1)) ∨ ((x27 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x27) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x27 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5052 (x06 x26 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x26)) ≤ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x26)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th278 x06 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause5053 (t x23 x26 x36 : ℝ) : ((¬ ((x23 + ((-1) * x36)) ≤ (-1))) ∨ ((t + ((-1) * x23) + x26) ≥ 1) ∨ ((t + ((-1) * x36)) ≤ 0) ∨ (¬ (x26 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x23 + ((-1) * x36)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x23) + x26) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x26 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th279 t x23 x26 x36
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u3 (And.intro u1 u0))))) h

theorem clause5054 (x26 : ℝ) (h : (x26 ≥ 0)) : ((x26 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x26 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause5055 (t x36 : ℝ) : ((¬ ((t + ((-1) * x36)) ≤ 0)) ∨ (t ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x36) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th281 t x36
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause5057 (t x36 : ℝ) : ((¬ (t ≤ x36)) ∨ (¬ (x36 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x36 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th282 t x36
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause5059 (t x36 : ℝ) (h : (x36 < t)) : ((x36 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 < t) := fun hh => hn hh
  exact u0 h

theorem clause5060 (t x02 x06 x23 x26 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((t + ((-1) * x23) + x26) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x23) + x26) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th284 t x02 x06 x23 x26 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u2 (And.intro u1 (And.intro u0 u5))))))) h

theorem clause5061 (t x02 x23 x34 x35 : ℝ) : ((¬ (x23 ≥ 0)) ∨ ((t + x34 + ((-1) * x35)) ≥ 1) ∨ (¬ ((x34 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x02)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ¬ ((t + ((-1) * x02)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
  have h := NineTheoryTrial.th285 t x02 x23 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u4 (And.intro u3 (And.intro u2 u1)))))) h

theorem clause5062 (t x03 x06 x34 x35 x36 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x34 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x35)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x34 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x03 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th286 t x03 x06 x34 x35 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u3 (And.intro u1 (And.intro u6 (And.intro u0 (And.intro u5 u2)))))))) h

theorem clause5063 (t x01 x03 x13 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ ((t + x01 + ((-1) * x03)) ≥ 1) ∨ (¬ (x13 ≥ 0)) ∨ ((t + ((-1) * x03)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + x01 + ((-1) * x03)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ¬ ((t + ((-1) * x03)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th288 t x01 x03 x13
  exact (fun hh => (fun hh => hh) (hh (And.intro u3 (And.intro u1 (And.intro u2 u0))))) h

theorem clause5064 (t x01 x02 x14 x23 x35 x46 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((t + x01 + ((-1) * x02)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((t + ((-1) * x46) + x56) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((x35 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((t + x01 + ((-1) * x02)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x23 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + ((-1) * x46) + x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th289 t x01 x02 x14 x23 x35 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u6 (And.intro u1 (And.intro u3 (And.intro u7 (And.intro u5 (And.intro u4 u2))))))))) h

theorem clause5065 (t x01 x06 x14 x26 x45 x56 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1))) ∨ (¬ ((t + x01 + ((-1) * x06)) ≥ 1)) ∨ (¬ ((x14 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + x26 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x26 + ((-1) * x67)) ≤ (-1)))) := by
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
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((t + x01 + ((-1) * x06)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((t + x26 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ((x26 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th290 t x01 x06 x14 x26 x45 x56 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u2 (And.intro u7 (And.intro u6 (And.intro u5 u3))))))))) h

theorem clause5066 (x34 : ℝ) (h : (x34 ≥ 0)) : ((x34 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause5067 (x14 x46 : ℝ) : ((¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x14 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th292 x14 x46
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause5068 (x06 x16 x46 : ℝ) : (((x06 + ((-1) * x46)) ≤ 0) ∨ (¬ ((x16 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x16)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ((x16 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x16)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th293 x06 x16 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause5069 (t x06 x34 x36 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x34 + ((-1) * x36)) ≤ 0)) ∨ (¬ ((t + x45 + ((-1) * x46)) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x45 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th294 t x06 x34 x36 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u5 (And.intro u4 (And.intro u2 (And.intro u6 u3)))))))) h

theorem clause5070 (x06 x36 x46 x67 : ℝ) : ((¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x46)) ≤ 0) := by
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
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th295 x06 x36 x46 x67
  exact (fun hh => (fun hh => hh u0) (hh (And.intro u2 (And.intro u1 u3)))) h

theorem clause5071 (x03 x34 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x35)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x35)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th296 x03 x34 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause5072 (x01 x13 x14 : ℝ) : ((¬ ((x01 + ((-1) * x13)) ≥ 1)) ∨ (¬ ((x13 + ((-1) * x14)) ≥ 0)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x01 + ((-1) * x13)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x13 + ((-1) * x14)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th297 x01 x13 x14
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 u2)))) h

theorem clause5073 (x01 x03 x14 x34 : ℝ) : ((¬ ((x14 + ((-1) * x34)) ≤ 0)) ∨ (¬ ((x01 + ((-1) * x03)) ≥ 0)) ∨ (¬ ((x03 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x01 + ((-1) * x14)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x14 + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x01 + ((-1) * x03)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x03 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x01 + ((-1) * x14)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th298 x01 x03 x14 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 (And.intro u3 u2))))) h

theorem clause5074 (x03 x13 x35 : ℝ) : ((¬ ((x03 + ((-1) * x35)) ≥ 1)) ∨ (¬ ((x03 + ((-1) * x13)) ≤ 0)) ∨ (¬ ((x13 + ((-1) * x35)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x35)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x03 + ((-1) * x13)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x13 + ((-1) * x35)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th299 x03 x13 x35
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause5075 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x35)) ≥ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5077 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x13 + ((-1) * x15)) ≤ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5081 (t x13 x15 x35 : ℝ) : (((x15 + ((-1) * x35)) ≤ 0) ∨ ((x13 + ((-1) * x15)) ≥ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5082 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x15 + ((-1) * x35)) ≤ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5085 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((x15 + ((-1) * x35)) ≥ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5086 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((x13 + ((-1) * x15)) ≥ 0) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5087 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x13 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5088 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x15) ≥ 1) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5089 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x15) + x35) ≥ 1) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x15) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5097 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((t + x15 + ((-1) * x35)) ≥ 1) ∨ (¬ (x13 ≤ x15)) ∨ (¬ (x15 ≤ x35)) ∨ (¬ ((x35 - x13) ≥ 1)) ∨ (¬ ((x15 - x13) ≤ (t - 1))) ∨ (¬ ((x35 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x15 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x13 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x35) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x35 - x13) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x13) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x35 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5100 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5102 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x13 + ((-1) * x15)) ≤ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5103 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x15)) ≤ 0) ∨ ((t + ((-1) * x13) + x15) ≥ 1) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5106 (t x13 x15 x35 : ℝ) : (((x15 + ((-1) * x35)) ≤ 0) ∨ ((x13 + ((-1) * x15)) ≥ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5107 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x15 + ((-1) * x35)) ≤ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5110 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((x15 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5111 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((x13 + ((-1) * x15)) ≥ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5112 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((x13 + ((-1) * x35)) ≤ (-1)) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5113 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x13) + x15) ≥ 1) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x13) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5114 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≤ (-1)) ∨ ((t + ((-1) * x15) + x35) ≥ 1) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x15) + x35) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5120 (t x13 x15 x35 : ℝ) : (((t + x15 + ((-1) * x35)) ≥ 1) ∨ ((x15 + ((-1) * x35)) ≥ 0) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x15 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x35)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5122 (t x13 x15 x35 : ℝ) : (((x13 + ((-1) * x35)) ≥ 1) ∨ ((t + x15 + ((-1) * x35)) ≥ 1) ∨ (¬ (x35 ≤ x15)) ∨ (¬ (x15 ≤ x13)) ∨ (¬ ((x13 - x35) ≥ 1)) ∨ (¬ ((x13 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x35) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x13 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x15 + ((-1) * x35)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x35 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x13) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x13 - x35) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x13 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x35) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th301 t x13 x15 x35
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5175 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x13 ≤ x15) ∨ (x35 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5176 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x13 ≤ x15) ∨ (x15 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5177 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x13 ≤ x15) ∨ ((x13 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5178 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x13 ≤ x15) ∨ ((x13 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5179 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x13 ≤ x15) ∨ ((x15 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x13 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5180 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x15 ≤ x35) ∨ (x35 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5181 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x15 ≤ x35) ∨ (x15 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5182 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x15 ≤ x35) ∨ ((x13 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5183 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x15 ≤ x35) ∨ ((x13 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5184 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : ((x15 ≤ x35) ∨ ((x15 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x35) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5185 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x13) ≥ 1) ∨ (x35 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5186 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x13) ≥ 1) ∨ (x15 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5187 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x13) ≥ 1) ∨ ((x13 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5188 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x13) ≥ 1) ∨ ((x13 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5189 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x13) ≥ 1) ∨ ((x15 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x13) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5190 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x15 - x13) ≤ (t - 1)) ∨ (x35 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5191 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x15 - x13) ≤ (t - 1)) ∨ (x15 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5192 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x15 - x13) ≤ (t - 1)) ∨ ((x13 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5193 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x15 - x13) ≤ (t - 1)) ∨ ((x13 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5194 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x15 - x13) ≤ (t - 1)) ∨ ((x15 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 - x13) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5195 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x15) ≤ (t - 1)) ∨ (x35 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x35 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5196 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x15) ≤ (t - 1)) ∨ (x15 ≤ x13)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x13) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5197 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x15) ≤ (t - 1)) ∨ ((x13 - x35) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x35) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5198 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x15) ≤ (t - 1)) ∨ ((x13 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x13 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5199 (t x13 x15 x35 : ℝ) (h : (((x13 ≤ x15) ∧ (x15 ≤ x35) ∧ ((x35 - x13) ≥ 1) ∧ ((x15 - x13) ≤ (t - 1)) ∧ ((x35 - x15) ≤ (t - 1))) ∨ ((x35 ≤ x15) ∧ (x15 ≤ x13) ∧ ((x13 - x35) ≥ 1) ∧ ((x13 - x15) ≤ (t - 1)) ∧ ((x15 - x35) ≤ (t - 1))))) : (((x35 - x15) ≤ (t - 1)) ∨ ((x15 - x35) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x35 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x35) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5200 (x15 x35 x56 : ℝ) : ((¬ ((x35 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((x15 + ((-1) * x35)) ≥ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x35 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x15 + ((-1) * x35)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x15 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th303 x15 x35 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause5201 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x16)) ≤ 0) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5203 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x16)) ≤ 0) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5207 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((x15 + ((-1) * x16)) ≥ 0) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5208 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5210 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x16) + x56) ≥ 1) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5211 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5212 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x15 + ((-1) * x16)) ≥ 0) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5213 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5215 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x56) ≥ 1) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5221 (t x15 x16 x56 : ℝ) : (((t + x16 + ((-1) * x56)) ≥ 1) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x15 ≤ x16)) ∨ (¬ (x16 ≤ x56)) ∨ (¬ ((x56 - x15) ≥ 1)) ∨ (¬ ((x16 - x15) ≤ (t - 1))) ∨ (¬ ((x56 - x16) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x16 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x15 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x15) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x16 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5226 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x16)) ≤ 0) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5228 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x16)) ≤ 0) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x16)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5232 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((x15 + ((-1) * x16)) ≥ 0) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5233 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5235 (t x15 x16 x56 : ℝ) : (((x16 + ((-1) * x56)) ≤ 0) ∨ ((t + ((-1) * x16) + x56) ≥ 1) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5236 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5237 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x15 + ((-1) * x16)) ≥ 0) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x16)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5238 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((x15 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5240 (t x15 x16 x56 : ℝ) : (((x15 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x16) + x56) ≥ 1) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x16) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5246 (t x15 x16 x56 : ℝ) : (((t + x16 + ((-1) * x56)) ≥ 1) ∨ ((x16 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x16)) ∨ (¬ (x16 ≤ x15)) ∨ (¬ ((x15 - x56) ≥ 1)) ∨ (¬ ((x15 - x16) ≤ (t - 1))) ∨ (¬ ((x16 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x16 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x16) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x16 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x16) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x16 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th305 t x15 x16 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5301 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x15 ≤ x16) ∨ (x56 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5302 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x15 ≤ x16) ∨ (x16 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5303 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x15 ≤ x16) ∨ ((x15 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5304 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x15 ≤ x16) ∨ ((x15 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5305 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x15 ≤ x16) ∨ ((x16 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x16) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5306 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x16 ≤ x56) ∨ (x56 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5307 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x16 ≤ x56) ∨ (x16 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5308 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x16 ≤ x56) ∨ ((x15 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5309 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x16 ≤ x56) ∨ ((x15 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5310 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : ((x16 ≤ x56) ∨ ((x16 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x16 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5311 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x15) ≥ 1) ∨ (x56 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5312 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x15) ≥ 1) ∨ (x16 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5313 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x15) ≥ 1) ∨ ((x15 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5314 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x15) ≥ 1) ∨ ((x15 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5315 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x15) ≥ 1) ∨ ((x16 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x15) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5316 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x16 - x15) ≤ (t - 1)) ∨ (x56 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5317 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x16 - x15) ≤ (t - 1)) ∨ (x16 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5318 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x16 - x15) ≤ (t - 1)) ∨ ((x15 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5319 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x16 - x15) ≤ (t - 1)) ∨ ((x15 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5320 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x16 - x15) ≤ (t - 1)) ∨ ((x16 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x16 - x15) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5321 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x16) ≤ (t - 1)) ∨ (x56 ≤ x16)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x16) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5322 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x16) ≤ (t - 1)) ∨ (x16 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x16 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5323 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x16) ≤ (t - 1)) ∨ ((x15 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5324 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x16) ≤ (t - 1)) ∨ ((x15 - x16) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x16) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5325 (t x15 x16 x56 : ℝ) (h : (((x15 ≤ x16) ∧ (x16 ≤ x56) ∧ ((x56 - x15) ≥ 1) ∧ ((x16 - x15) ≤ (t - 1)) ∧ ((x56 - x16) ≤ (t - 1))) ∨ ((x56 ≤ x16) ∧ (x16 ≤ x15) ∧ ((x15 - x56) ≥ 1) ∧ ((x15 - x16) ≤ (t - 1)) ∧ ((x16 - x56) ≤ (t - 1))))) : (((x56 - x16) ≤ (t - 1)) ∨ ((x16 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x16) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x16 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5326 (t x02 x15 x25 x26 x56 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x26 + ((-1) * x56)) ≤ 0)) ∨ (¬ ((x15 + ((-1) * x56)) ≥ 1)) ∨ (¬ ((t + ((-1) * x15) + x25) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x26 + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x15 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((t + ((-1) * x15) + x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th307 t x02 x15 x25 x26 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u2 (And.intro u3 u1))))))) h

theorem clause5327 (x02 x25 x26 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x26)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x26)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x26)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x25 + ((-1) * x26)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th308 x02 x25 x26
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause5328 (t x15 : ℝ) : ((¬ ((t + ((-1) * x15)) ≤ 0)) ∨ (t ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x15)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x15) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th310 t x15
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause5330 (t x15 : ℝ) : ((¬ (t ≤ x15)) ∨ (¬ (x15 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x15 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th311 t x15
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause5332 (t x15 : ℝ) (h : (x15 < t)) : ((x15 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 < t) := fun hh => hn hh
  exact u0 h

theorem clause5333 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x25)) ≥ 0) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5335 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5336 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((t + ((-1) * x12) + x15) ≥ 1) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5340 (t x12 x15 x25 : ℝ) : (((x15 + ((-1) * x25)) ≤ 0) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5342 (t x12 x15 x25 : ℝ) : (((t + ((-1) * x15) + x25) ≥ 1) ∨ ((x15 + ((-1) * x25)) ≤ 0) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x15) + x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5343 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x15 + ((-1) * x25)) ≥ 0) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5344 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x12 + ((-1) * x15)) ≥ 0) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5345 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5347 (t x12 x15 x25 : ℝ) : (((t + ((-1) * x15) + x25) ≥ 1) ∨ ((x12 + ((-1) * x25)) ≤ (-1)) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x15) + x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5350 (t x12 x15 x25 : ℝ) : (((t + x12 + ((-1) * x15)) ≥ 1) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5353 (t x12 x15 x25 : ℝ) : (((t + x15 + ((-1) * x25)) ≥ 1) ∨ ((x15 + ((-1) * x25)) ≥ 0) ∨ (¬ (x12 ≤ x15)) ∨ (¬ (x15 ≤ x25)) ∨ (¬ ((x25 - x12) ≥ 1)) ∨ (¬ ((x15 - x12) ≤ (t - 1))) ∨ (¬ ((x25 - x15) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x15 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x12 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 - x12) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x15 - x12) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5358 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((x15 + ((-1) * x25)) ≥ 0) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5360 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5361 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x15)) ≤ 0) ∨ ((t + ((-1) * x12) + x15) ≥ 1) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x15)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x12) + x15) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5364 (t x12 x15 x25 : ℝ) : (((x15 + ((-1) * x25)) ≤ 0) ∨ ((x12 + ((-1) * x15)) ≥ 0) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5365 (t x12 x15 x25 : ℝ) : (((x15 + ((-1) * x25)) ≤ 0) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x15 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5368 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x15 + ((-1) * x25)) ≥ 0) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5369 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x12 + ((-1) * x15)) ≥ 0) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5370 (t x12 x15 x25 : ℝ) : (((x12 + ((-1) * x25)) ≤ (-1)) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5372 (t x12 x15 x25 : ℝ) : (((t + ((-1) * x15) + x25) ≥ 1) ∨ ((x12 + ((-1) * x25)) ≤ (-1)) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x15) + x25) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5374 (t x12 x15 x25 : ℝ) : (((t + x12 + ((-1) * x15)) ≥ 1) ∨ ((x12 + ((-1) * x15)) ≥ 0) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x12 + ((-1) * x15)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x15)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5380 (t x12 x15 x25 : ℝ) : (((t + x15 + ((-1) * x25)) ≥ 1) ∨ ((x12 + ((-1) * x25)) ≥ 1) ∨ (¬ (x25 ≤ x15)) ∨ (¬ (x15 ≤ x12)) ∨ (¬ ((x12 - x25) ≥ 1)) ∨ (¬ ((x12 - x15) ≤ (t - 1))) ∨ (¬ ((x15 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x15 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x25 ≤ x15) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x15 ≤ x12) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x12 - x25) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x12 - x15) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x15 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th314 t x12 x15 x25
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause5433 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x12 ≤ x15) ∨ (x25 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5434 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x12 ≤ x15) ∨ (x15 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5435 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x12 ≤ x15) ∨ ((x12 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5436 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x12 ≤ x15) ∨ ((x12 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5437 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x12 ≤ x15) ∨ ((x15 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x12 ≤ x15) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5438 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x15 ≤ x25) ∨ (x25 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5439 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x15 ≤ x25) ∨ (x15 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5440 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x15 ≤ x25) ∨ ((x12 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause5441 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x15 ≤ x25) ∨ ((x12 - x15) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x15) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause5442 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : ((x15 ≤ x25) ∨ ((x15 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x15 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x15 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause5443 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x12) ≥ 1) ∨ (x25 ≤ x15)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x15) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause5444 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x12) ≥ 1) ∨ (x15 ≤ x12)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x15 ≤ x12) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause5445 (t x12 x15 x25 : ℝ) (h : (((x12 ≤ x15) ∧ (x15 ≤ x25) ∧ ((x25 - x12) ≥ 1) ∧ ((x15 - x12) ≤ (t - 1)) ∧ ((x25 - x15) ≤ (t - 1))) ∨ ((x25 ≤ x15) ∧ (x15 ≤ x12) ∧ ((x12 - x25) ≥ 1) ∧ ((x12 - x15) ≤ (t - 1)) ∧ ((x15 - x25) ≤ (t - 1))))) : (((x25 - x12) ≥ 1) ∨ ((x12 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x12) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x12 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

#print axioms clause5445
end NineCNFDirectTrial
